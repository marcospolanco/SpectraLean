/-
  Heat_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Heat` (Phase B, Steps 1–3 of
  `proposals/reversibility-and-heat-semigroup.md`): the heat semigroup
  `e^{-tL}` — identity at time zero, symmetry, the semigroup law, and
  mass conservation — instantiated at concrete `Fin 2` networks (the
  edge `K₂`, symmetric, and an asymmetric fixture whose Laplacian
  `!![1,-1;1,-1]` is square-zero, which makes `heatKernel` computable
  in closed form at *every* time through the square-zero collapse
  `exp_neg_smul_eq_one_add_of_mul_self_eq_zero`), plus a disconnected
  `Fin 3` fixture for the per-component no-leakage witness.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Heat
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Fixtures
-/

/-- Adjacency of the two-vertex complete graph `K₂`: symmetric, unit
weights, degrees (1, 1). -/
def edgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

theorem edgeAdj_isSymm : edgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [edgeAdj]

/-- The asymmetric fixture: `A = !![0, 1; -1, 0]]` — degrees `(1, -1)`,
so its Laplacian is `!![1, -1; 1, -1]]`, a *square-zero* nonzero matrix.
This is the closed-form handle: `heatKernel asymAdj 1` evaluates exactly
through `exp_eq_one_add_of_mul_self_eq_zero`. -/
def asymAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0]

theorem asymAdj_not_isSymm : ¬ asymAdj.IsSymm := by
  intro h
  have h01 : asymAdj 1 0 = asymAdj 0 1 := Matrix.IsSymm.apply h 0 1
  simp [asymAdj] at h01
  norm_num at h01

theorem asymLaplacian : laplacian asymAdj = !![1, -1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, asymAdj, Fin.sum_univ_two]

theorem asymLaplacian_sq : laplacian asymAdj * laplacian asymAdj = 0 := by
  rw [asymLaplacian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-!
## Identity at time zero
-/

/-- At time zero the semigroup is the identity on the symmetric fixture:
all four entries computed. -/
theorem heatKernel_zero_edge_QA :
    heatKernel edgeAdj 0 = !![1, 0; 0, 1] := by
  rw [heatKernel_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-- The identity at time zero is hypothesis-free: it also holds on the
asymmetric fixture, where the symmetry theorem does not apply. -/
theorem heatKernel_zero_asym_QA :
    heatKernel asymAdj 0 = !![1, 0; 0, 1] := by
  rw [heatKernel_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

/-!
## Symmetry
-/

/-- Symmetry on the symmetric fixture through the theorem, at every
time, with the hypothesis *derived* from the literal (not assumed):
had `heatKernel_isSymm` gone through a wrong exponent (say a transpose
defect), this instantiation would still typecheck but its use in the
entry-level fixture below would not compose. -/
theorem heatKernel_isSymm_edge_QA (t : ℝ) : (heatKernel edgeAdj t).IsSymm :=
  heatKernel_isSymm edgeAdj edgeAdj_isSymm t

set_option linter.unnecessarySeqFocus false in
/-- Closed form at `t = 1` on the square-zero-Laplacian fixture:
`e^{-L} = 1 + (-L) = !![0, 1; -1, 2]]`, every entry computed. Any defect
in the exponent's shape — a dropped `t`, a wrong scalar action, a
mis-negated Laplacian — changes this value. -/
theorem heatKernel_asym_value_QA :
    heatKernel asymAdj 1 = !![0, 1; -1, 2] := by
  rw [heatKernel, one_smul,
    exp_eq_one_add_of_mul_self_eq_zero _ (by rw [neg_mul_neg, asymLaplacian_sq]),
    asymLaplacian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- On the asymmetric fixture the hypothesis-free symmetry statement is
refuted: `heatKernel asymAdj 1` is computed exactly (square-zero
collapse) and its `(0,1)`/`(1,0)` entries disagree, while `hA` is
provably violated at the same pair (`asymAdj_not_isSymm`) — the
symmetry hypothesis of `heatKernel_isSymm` is load-bearing, not
decorative. -/
theorem heatKernel_asym_not_isSymm_QA : ¬ (heatKernel asymAdj 1).IsSymm := by
  intro h
  have h01 : heatKernel asymAdj 1 1 0 = heatKernel asymAdj 1 0 1 :=
    Matrix.IsSymm.apply h 0 1
  rw [heatKernel_asym_value_QA] at h01
  simp at h01
  norm_num at h01

/-!
## Exact value and the load-bearing sign
-/

/-- The sign in the exponent is load-bearing: with `+1 • laplacian`
instead of `-1 • laplacian` the value differs (entrywise at `(0, 0)`:
`0 ≠ 2`). Pins the definition's negation and scalar action against a
concretely evaluated alternative. -/
theorem heatKernel_sign_QA :
    heatKernel asymAdj 1 ≠ NormedSpace.exp ℝ (1 • laplacian asymAdj) := by
  intro h
  rw [heatKernel_asym_value_QA, one_smul,
    exp_eq_one_add_of_mul_self_eq_zero _ asymLaplacian_sq, asymLaplacian] at h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00
  norm_num at h00

/-!
## The semigroup law (Step 2)
-/

set_option linter.unnecessarySeqFocus false in
/-- Closed form at *every* time on the square-zero fixture:
`heatKernel asymAdj t = !![1 - t, t; -t, 1 + t]`, all four entries
computed for symbolic `t`. Any defect in the exponent's shape — a
dropped `t`, a wrong scalar action — changes this matrix. -/
theorem heatKernel_asym_closed_QA (t : ℝ) :
    heatKernel asymAdj t = !![1 - t, t; -t, 1 + t] := by
  rw [heatKernel, exp_neg_smul_eq_one_add_of_mul_self_eq_zero _
    asymLaplacian_sq, asymLaplacian]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

set_option linter.unnecessarySeqFocus false in
/-- The raw-arithmetic route to the semigroup law on the fixture: both
sides' closed forms multiplied by hand (`Matrix.mul` on literals) equal
the closed form at `s + t`, every entry by `ring` — *independent* of the
semigroup theorem. A wrong time-combination constant anywhere in the
theorem would contradict this hand computation. -/
theorem heatKernel_asym_semigroup_raw_QA (s t : ℝ) :
    (!![1 - s, s; -s, 1 + s] : Matrix (Fin 2) (Fin 2) ℝ) * !![1 - t, t; -t, 1 + t]
      = !![1 - (s + t), s + t; -(s + t), 1 + (s + t)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring

/-- The theorem route to the *same* statement: the semigroup law
composed with one closed form. Two independent proofs of one
closed-form identity — the interface check: the delivered theorem really
computes the hand value. -/
theorem heatKernel_asym_semigroup_theorem_QA (s t : ℝ) :
    heatKernel asymAdj s * heatKernel asymAdj t
      = !![1 - (s + t), s + t; -(s + t), 1 + (s + t)] :=
  (heatKernel_mul_heatKernel asymAdj s t).trans (heatKernel_asym_closed_QA (s + t))

/-- Fully numeric instance at `s = 2`, `t = 3`: both times' kernels and
their product's value `!![-4, 5; -5, 6]` all concrete. -/
theorem heatKernel_asym_semigroup_numeric_QA :
    heatKernel asymAdj 2 * heatKernel asymAdj 3 = !![-4, 5; -5, 6] := by
  rw [heatKernel_asym_semigroup_theorem_QA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- The group property instance: flowing forward one unit and then
backward one unit is the identity — the semigroup law composed with the
time-zero identity, the two interface items of the external consumer
working together. -/
theorem heatKernel_asym_group_QA :
    heatKernel asymAdj 1 * heatKernel asymAdj (-1) = 1 := by
  rw [heatKernel_mul_heatKernel, add_neg_cancel, heatKernel_zero]

/-- The law instantiates at the identity element on the symmetric K₂
fixture (where no closed form exists): `t = 0` on the left. -/
theorem heatKernel_semigroup_zero_left_QA (t : ℝ) :
    heatKernel edgeAdj 0 * heatKernel edgeAdj t = heatKernel edgeAdj t := by
  rw [heatKernel_mul_heatKernel, zero_add]

/-- …and `t = 0` on the right. -/
theorem heatKernel_semigroup_zero_right_QA (t : ℝ) :
    heatKernel edgeAdj t * heatKernel edgeAdj 0 = heatKernel edgeAdj t := by
  rw [heatKernel_mul_heatKernel, add_zero]

/-!
## Mass conservation (Step 3)
-/

/-- The interface chain's base, checked raw on the fixture: the pinned
Laplacian `!![1, -1; 1, -1]]` multiplies `onesVec` to the zero vector by
hand (`funext` + literal arithmetic) — the exact instance of
`laplacian_ones_in_kernel` the conservation theorem consumes, verified
independently of that theorem. -/
theorem asymLaplacian_mulVec_ones_raw_QA :
    laplacian asymAdj *ᵥ onesVec = 0 := by
  rw [asymLaplacian]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_two]

/-- Mass conservation at every time on the asymmetric fixture, through
the Step-3 theorem. No symmetry hypothesis exists to be violated here
(`asymAdj_not_isSymm`), so this instance genuinely exercises the
hypothesis-free statement. -/
theorem heatKernel_ones_conserved_asym_QA (t : ℝ) :
    heatKernel asymAdj t *ᵥ onesVec = onesVec :=
  heatKernel_mulVec_onesVec asymAdj t

/-- The raw-arithmetic route to the *same* statement: the fixture's
closed form `!![1 - t, t; -t, 1 + t]]` multiplied onto `onesVec` by
hand, every entry `ring` — *independent* of the Step-3 theorem. A wrong
conservation anywhere in the delivered chain (a stray transpose, a
wrong exponent sign) contradicts this hand computation. -/
theorem heatKernel_ones_conserved_raw_QA (t : ℝ) :
    (!![1 - t, t; -t, 1 + t] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ onesVec = onesVec := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_two]

/-- Mass conservation on the symmetric `K₂` fixture (where no closed
form exists): the theorem route only. The point: conservation does not
depend on the fixture's square-zero accident. -/
theorem heatKernel_ones_conserved_edge_QA (t : ℝ) :
    heatKernel edgeAdj t *ᵥ onesVec = onesVec :=
  heatKernel_mulVec_onesVec edgeAdj t

/-- The disconnected `Fin 3` fixture: the edge `{0, 1}` plus the
isolated vertex `2` — the matrix `!![0, 1, 0; 1, 0, 0; 0, 0, 0]`,
written as an entrywise function so that `simp`/`norm_num` can reduce
every entry (the `Fin 3` cons-literal applications resist `simp`'s
index-2 reduction at this pin). -/
def disAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0

/-- The `{0, 1}`-component indicator is `L`-harmonic on the
disconnected fixture, checked raw from the Laplacian definition
(entrywise `mulVec` through `laplacian`/`degreeMatrix`/`deg`/`disAdj`,
literal arithmetic) — the load-bearing half of the no-leakage witness
below: a mis-shaped `laplacian` (a stray symmetrized adjacency, a wrong
degree convention) breaks harmonicity and the witness with it. -/
theorem disLaplacian_mulVec_component_raw_QA :
    laplacian disAdj *ᵥ (fun j => if j = 2 then (0:ℝ) else 1) = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply, Fin.sum_univ_three,
      laplacian, degreeMatrix, deg, disAdj]

/-- **Heat does not cross components** (the proposal's named
negative-witness follow-on): the `{0, 1}`-component indicator is
`L`-harmonic, so the general engine `exp_mulVec_eq_of_mulVec_eq_zero`
fixes it at every time — mass is conserved *per component*, not merely
globally, so the conservation statement is not accidentally vacuous on
disconnected input. -/
theorem heatKernel_noLeakage_component_QA (t : ℝ) :
    heatKernel disAdj t *ᵥ (fun j => if j = 2 then (0:ℝ) else 1)
      = fun j => if j = 2 then (0:ℝ) else 1 := by
  rw [heatKernel]
  refine exp_mulVec_eq_of_mulVec_eq_zero _ _ ?_
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc,
    disLaplacian_mulVec_component_raw_QA, smul_zero, neg_zero]

/-- The isolated-vertex indicator is fixed too (the sharpest
no-cross-component case: the isolated vertex is a one-dimensional
component). -/
theorem heatKernel_isolated_fixed_QA (t : ℝ) :
    heatKernel disAdj t *ᵥ (fun j => if j = 2 then (1:ℝ) else 0)
      = fun j => if j = 2 then (1:ℝ) else 0 := by
  rw [heatKernel]
  refine exp_mulVec_eq_of_mulVec_eq_zero _ _ ?_
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc]
  have hker : laplacian disAdj *ᵥ (fun j => if j = 2 then (1:ℝ) else 0) = 0 := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply, Fin.sum_univ_three,
        laplacian, degreeMatrix, deg, disAdj]
  rw [hker, smul_zero, neg_zero]

/-- The kernel hypothesis of the engine is load-bearing: a non-kernel
vector is *not* fixed. On the square-zero fixture, `heatKernel 1`
evaluates exactly to `!![0, 1; -1, 2]]`, whose action on `![1, 0]`
is `![0, -1] ≠ ![1, 0]` — the hypothesis-free strengthening of
`exp_mulVec_eq_of_mulVec_eq_zero` is refuted with every other
structural fact intact. -/
theorem heatKernel_asym_not_fix_nonkernel_QA :
    heatKernel asymAdj 1 *ᵥ ![1, 0] ≠ ![1, 0] := by
  rw [heatKernel_asym_value_QA]
  intro h
  have h0 := congrFun h 0
  simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two] at h0

/-!
## Eigenmode decay and the DC limit (Step 4)
-/

open Filter

/-- The K₂ Laplacian, computed raw from the definition: degrees `(1, 1)`,
so `L = !![1, -1; -1, 1]`. -/
theorem edgeLaplacian_eq : laplacian edgeAdj = !![1, -1; -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, edgeAdj, Fin.sum_univ_two]

/-- The K₂ Laplacian squares to twice itself: `!![1, -1; -1, 1]` squared
is `!![2, -2; -2, 2]`, all entries by literal arithmetic. This is the
`M * M = c • M` hypothesis of the Step-4 collapse — checked raw,
independent of any theorem. -/
theorem edgeLaplacian_mul_smul :
    laplacian edgeAdj * laplacian edgeAdj = 2 • laplacian edgeAdj := by
  rw [edgeLaplacian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The K₂ Laplacian's hand eigenvector: `![1, -1]` has eigenvalue `2`
(`L *ᵥ ![1, -1] = ![2, -2] = 2 • ![1, -1]`), raw arithmetic — the
eigen-equation the mode-decay witnesses consume. -/
theorem edgeLaplacian_mulVec_mode :
    laplacian edgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)
      = (2 : ℝ) • (![1, -1] : Fin 2 → ℝ) := by
  rw [edgeLaplacian_eq]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, smul_eq_mul] <;>
    norm_num

/-- The K₂ Laplacian's action on the DC-offset witness `![1, 3]`:
`L *ᵥ ![1, 3] = ![-2, 2]`, raw arithmetic — consumed by the raw DC-limit
route. -/
theorem edgeLaplacian_mulVec_dc :
    laplacian edgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ) = (![ -2, 2] : Fin 2 → ℝ) := by
  rw [edgeLaplacian_eq]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two] <;> norm_num

/-- The closed form of the K₂ heat kernel at every nonzero time, through
the Step-4 rank-one-idempotent collapse (`c := -(2 * t)`; the square
`M² = -(2t) • M` verified through `edgeLaplacian_mul_smul`). This is
the symbolic-`t` exact-evaluation handle on the *symmetric* fixture —
no square-zero accident here. -/
theorem heatKernel_edge_closed_QA (t : ℝ) (ht : t ≠ 0) :
    heatKernel edgeAdj t
      = 1 + ((Real.exp (-(2 * t)) - 1) / 2) • laplacian edgeAdj := by
  rw [heatKernel]
  have hM : (-(t • laplacian edgeAdj)) * (-(t • laplacian edgeAdj))
      = (-(2 * t)) • (-(t • laplacian edgeAdj)) := by
    rw [edgeLaplacian_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, smul_eq_mul, Fin.sum_univ_two, neg_mul] <;>
      (try ring)
  have hc : (-(2 * t)) ≠ 0 := by
    rw [neg_ne_zero]
    exact mul_ne_zero two_ne_zero ht
  rw [exp_eq_one_add_of_mul_self_eq_smul _ hc hM, edgeLaplacian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;>
    (try field_simp) <;> (try ring)

/-- **Eigenmode decay on the symmetric fixture, engine route**: the heat
kernel acts on the hand eigenvector `![1, -1]` (eigenvalue `2`) by
exactly the decay factor `e^{-2t}` — the eigenmode theorem's engine at
every time `t` (no sign restriction). -/
theorem heatKernel_edge_mode_engine_QA (t : ℝ) :
    heatKernel edgeAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp (-(2 * t)) • (![1, -1] : Fin 2 → ℝ) := by
  rw [heatKernel]
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, edgeLaplacian_mulVec_mode,
    smul_smul, neg_smul]
  congr 2
  ring

set_option linter.unnecessarySeqFocus false in
/-- **Eigenmode decay on the symmetric fixture, raw route**: the same
statement through the closed form and hand arithmetic — `(1 + c • L) *ᵥ v
= v + 2c • v = e^{-2t} • v` — *independent* of the engine. Two routes to
one decay identity: a wrong sign, factor, or eigenvalue anywhere in
either delivered chain contradicts the other. -/
theorem heatKernel_edge_mode_raw_QA (t : ℝ) (ht : t ≠ 0) :
    heatKernel edgeAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp (-(2 * t)) • (![1, -1] : Fin 2 → ℝ) := by
  rw [heatKernel_edge_closed_QA t ht, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec_assoc, edgeLaplacian_mulVec_mode, smul_smul]
  have hcoef : (Real.exp (-(2 * t)) - 1) / 2 * 2 = Real.exp (-(2 * t)) - 1 :=
    div_mul_cancel₀ _ two_ne_zero
  rw [hcoef]
  funext i
  fin_cases i <;> simp [smul_eq_mul] <;> ring

/-- The all-ones `2 × 2` matrix: symmetric, with `![1, 1]` a hand
eigenvector of eigenvalue `2` (and squares to `2 • m2` — the second
`M * M = c • M` fixture). -/
def m2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun _ _ => 1

theorem m2_mulVec :
    m2 *ᵥ (![1, 1] : Fin 2 → ℝ) = (2 : ℝ) • (![1, 1] : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [m2, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, smul_eq_mul] <;>
    norm_num

theorem m2_mul_m2 : m2 * m2 = (2 : ℝ) • m2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m2, Matrix.mul_apply]

/-- The eigenmode engine at a *nonzero* eigenvalue: `exp m2` acts on the
hand eigenvector `![1, 1]` by `e²`. -/
theorem exp_m2_engine_QA :
    NormedSpace.exp ℝ m2 *ᵥ (![1, 1] : Fin 2 → ℝ)
      = Real.exp 2 • (![1, 1] : Fin 2 → ℝ) := by
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  exact m2_mulVec

/-- The rank-one-idempotent collapse on the second fixture: `exp m2 = 1 +
((e² - 1)/2) • m2`, through the raw square `m2 * m2 = 2 • m2`. -/
theorem exp_m2_collapse_QA :
    NormedSpace.exp ℝ m2 = 1 + ((Real.exp 2 - 1) / 2) • m2 :=
  exp_eq_one_add_of_mul_self_eq_smul m2 two_ne_zero m2_mul_m2

set_option linter.unnecessarySeqFocus false in
/-- **Cross-validation of the two Step-4 engines**: from the collapse's
value of `exp m2` alone, hand arithmetic recovers the engine's answer —
`(1 + ((e²-1)/2) • m2) *ᵥ ![1,1] = ![1,1] + (e²-1) • ![1,1] = e² •
![1,1]`. The eigenmode engine and the exponential collapse are two
independent constructions; this witness checks they compute the same
value. -/
theorem exp_m2_two_route_QA :
    (1 + ((Real.exp 2 - 1) / 2) • m2) *ᵥ (![1, 1] : Fin 2 → ℝ)
      = Real.exp 2 • (![1, 1] : Fin 2 → ℝ) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
    m2_mulVec, smul_smul, div_mul_cancel₀ _ two_ne_zero]
  funext i
  fin_cases i <;> simp [smul_eq_mul]

/-!
### The K₂ spectrum pinned, and the decay-monotonicity instantiation
-/

/-- A length-two list is the list of its two entries. -/
private theorem list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- Two-point spectrum pinning, both entries: a sorted length-two list
with sum `2` and product `0` is `[0, 2]`. -/
private theorem two_point_pin {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = 2)
    (hprod : l.prod = 0) :
    l.get ⟨0, by omega⟩ = 0 ∧ l.get ⟨1, by omega⟩ = 2 := by
  obtain ⟨g₀, g₁, hg⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, list_two_eq h2⟩
  subst hg
  have hmono : g₀ ≤ g₁ := hs.rel_get_of_lt (show (0 : Fin 2) < 1 by decide)
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with h0 | h1
  · constructor <;> simp <;> linarith
  · constructor <;> simp <;> linarith

/-- Trace and determinant of the K₂ Laplacian, entrywise. -/
theorem edgeLaplacian_trace : (laplacian edgeAdj).trace = 2 := by
  simp [Matrix.trace, edgeLaplacian_eq, Fin.sum_univ_two]; norm_num

theorem edgeLaplacian_det : (laplacian edgeAdj).det = 0 := by
  rw [edgeLaplacian_eq, Matrix.det_fin_two]
  norm_num

/-- **The K₂ Laplacian spectrum is `[0, 2]`**: sortedness plus trace
(`0 + 2 = 2`) and determinant (`0 * 2 = 0`) pin both entries — no axiom,
no spectral-theorem computation (the Cheeger QA pinning pattern, at the
combinatorial Laplacian). The two decay-factor QA theorems below read
their constants from here. -/
theorem edgeLaplacian_evals_QA :
    evals (laplacian_symmetric edgeAdj edgeAdj_isSymm) ⟨0, by simp⟩ = 0 ∧
      evals (laplacian_symmetric edgeAdj edgeAdj_isSymm) ⟨1, by simp⟩ = 2 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric edgeAdj
          edgeAdj_isSymm)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric edgeAdj
          edgeAdj_isSymm)).eigenvalues))).Sorted (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric edgeAdj
          edgeAdj_isSymm)).eigenvalues))).sum = 2 := by
    have htr : ∑ i : Fin 2, eigvalOf (laplacian edgeAdj)
        (laplacian_symmetric edgeAdj edgeAdj_isSymm) i = 2 := by
      rw [eigvalOf_sum_eq_trace, edgeLaplacian_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric edgeAdj
          edgeAdj_isSymm)).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2, ((isHermitian_of_isSymm
        (laplacian_symmetric edgeAdj edgeAdj_isSymm)).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm (laplacian_symmetric edgeAdj
        edgeAdj_isSymm)).det_eq_prod_eigenvalues
      rw [edgeLaplacian_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact two_point_pin hlen hsorted hsum hprod

/-- **The decay-monotonicity instantiation**: on K₂ at `t = 1`, the
higher mode's factor `e^{-2}` is at most the lower mode's factor
`e^{0} = 1` — the antitone theorem with both spectrum entries read from
the independently pinned `edgeLaplacian_evals_QA`. A defective ordering
or eigenvalue in the theorem would flip or misplace this numeric. -/
theorem heatKernel_decay_antitone_edge_QA : Real.exp (-2 : ℝ) ≤ 1 := by
  have h := heatKernel_decayFactor_antitone edgeAdj edgeAdj_isSymm
    (by norm_num : (0 : ℝ) ≤ 1)
    (show ((⟨0, by simp⟩ : Fin (Fintype.card (Fin 2)))
        ≤ (⟨1, by simp⟩ : Fin (Fintype.card (Fin 2)))) by
      simp [Fintype.card_fin])
  rw [(edgeLaplacian_evals_QA).1, (edgeLaplacian_evals_QA).2,
    show ((1 : ℝ) * 2) = 2 by norm_num, show ((1 : ℝ) * 0) = 0 by norm_num,
    neg_zero, Real.exp_zero] at h
  exact h

/-!
### The DC limit, two routes
-/

theorem edgeAdj_nonneg : ∀ i j, 0 ≤ edgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [edgeAdj]

theorem edge_adj01 : (supportGraph edgeAdj edgeAdj_isSymm).Adj
    (0 : Fin 2) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [edgeAdj]⟩

/-- The support graph of K₂ is connected (the single edge is a walk
between the two vertices). -/
theorem edgeAdj_supportGraph_connected :
    (supportGraph edgeAdj edgeAdj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons edge_adj01 SimpleGraph.Walk.nil⟩

/-- **The DC limit, theorem route**: on K₂, the heat flow of `![1, 3]`
converges to the mean `![2, 2]` — the Step-4 payoff theorem instantiated
on the fixture, the mean vector computed by hand
(`(∑ ![1,3])/2 • onesVec = 2 • onesVec = ![2,2]`). -/
theorem heatKernel_edge_dc_theorem_QA :
    Filter.Tendsto (fun t : ℝ => heatKernel edgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ))
      Filter.atTop (nhds (![2, 2] : Fin 2 → ℝ)) := by
  have h := heatKernel_mulVec_tendsto_atTop edgeAdj edgeAdj_isSymm
    edgeAdj_nonneg edgeAdj_supportGraph_connected (![1, 3] : Fin 2 → ℝ)
  have hmean : ((∑ j : Fin 2, (![1, 3] : Fin 2 → ℝ) j)
      / (Fintype.card (Fin 2) : ℝ)) • (onesVec : Fin 2 → ℝ)
      = (![2, 2] : Fin 2 → ℝ) := by
    rw [Fin.sum_univ_two]
    funext i
    fin_cases i <;> simp [onesVec, smul_eq_mul] <;> norm_num
  rwa [hmean] at h

set_option linter.unnecessarySeqFocus false in
/-- **The DC limit, raw route**: the same convergence computed from the
closed form — `heatKernel K₂ t *ᵥ ![1, 3] = ![2 - e^{-2t}, 2 + e^{-2t}]`
(by hand: `![1,3] + ((e^{-2t}-1)/2) • ![-2, 2]`), with each component
tending to `2` by the scalar decay-factor lemma `tendsto_exp_neg_mul_atTop`
— *independent* of the DC theorem, the kernel characterization, PSD,
and the eigenbasis. Two routes to one limit statement. -/
theorem heatKernel_edge_dc_raw_QA :
    Filter.Tendsto (fun t : ℝ => heatKernel edgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ))
      Filter.atTop (nhds (![2, 2] : Fin 2 → ℝ)) := by
  have hev : ∀ t : ℝ, t ≠ 0 → heatKernel edgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ)
      = (![2 - Real.exp (-(2 * t)), 2 + Real.exp (-(2 * t))] : Fin 2 → ℝ) := by
    intro t ht
    rw [heatKernel_edge_closed_QA t ht, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec_assoc, edgeLaplacian_mulVec_dc]
    funext i
    fin_cases i <;> norm_num [smul_eq_mul, neg_mul, Fin.sum_univ_two] <;> ring
  have hscalar : Filter.Tendsto (fun t : ℝ => Real.exp (-(2 * t)))
      Filter.atTop (nhds 0) := by
    refine (tendsto_exp_neg_mul_atTop (by norm_num : (0 : ℝ) < 2)).congr
      fun t => ?_
    congr 1
    ring
  have hraw : Filter.Tendsto
      (fun t : ℝ => (![2 - Real.exp (-(2 * t)),
        2 + Real.exp (-(2 * t))] : Fin 2 → ℝ))
      Filter.atTop (nhds (![2, 2] : Fin 2 → ℝ)) := by
    rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · simpa using tendsto_const_nhds.sub hscalar
    · simpa using tendsto_const_nhds.add hscalar
  refine hraw.congr' (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t = 0
  · subst ht
    show (![2 - Real.exp (-(2 * 0)), 2 + Real.exp (-(2 * 0))] : Fin 2 → ℝ)
        = heatKernel edgeAdj 0 *ᵥ (![1, 3] : Fin 2 → ℝ)
    have h1 : heatKernel edgeAdj 0 *ᵥ (![1, 3] : Fin 2 → ℝ)
        = (![1, 3] : Fin 2 → ℝ) := by
      rw [heatKernel_zero, Matrix.one_mulVec]
    rw [h1, show -(2 * 0) = (0 : ℝ) by ring, Real.exp_zero]
    funext i
    fin_cases i <;> norm_num
  · exact (hev t ht).symm

end SpectralGraphTheory.QA
