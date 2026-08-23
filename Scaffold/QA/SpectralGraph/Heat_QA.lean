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
  `Fin 3` fixture for the per-component no-leakage witness; Step 4
  (eigenmode decay, the DC limit); Phase C Step 1 (the heat-flow
  derivative at zero, two independent routes plus the infinitesimal
  conservation cross-check); and Phase C Step 2 (the first-order
  remainder bound: the K₂ eigenvalue inventory, the eigen-sum constant
  `4`, the concrete-bound witness cross-checked against the closed-form
  exponential value at two times, and the boundary-degradation witness
  pinning the `t²` scaling and the `t = 1/2` window fence).

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

/-!
## The heat-flow derivative at zero (Phase C, Step 1)
-/

/-- **The derivative value on K₂, theorem route**: the flow of `![1, 3]`
differentiates at `t = 0` to `![2, -2]` — the Phase C theorem instantiated
on the symmetric fixture, the Laplacian action `L *ᵥ ![1,3] = ![-2,2]`
supplied by the raw entrywise computation `edgeLaplacian_mulVec_dc`
(already verified independent of every Phase C theorem). -/
theorem heatKernel_edge_deriv_theorem_QA :
    HasDerivAt (fun t : ℝ => heatKernel edgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ))
      (![2, -2] : Fin 2 → ℝ) 0 := by
  have h := heatKernel_mulVec_hasDerivAt_zero edgeAdj edgeAdj_isSymm
    (![1, 3] : Fin 2 → ℝ)
  rw [edgeLaplacian_mulVec_dc] at h
  have hval : (-(![-2, 2] : Fin 2 → ℝ)) = ![2, -2] := by
    funext i
    fin_cases i <;> simp
  rw [hval] at h
  exact h

set_option linter.unnecessarySeqFocus false in
/-- **The derivative value on K₂, raw route**: the same statement through
the Step-4 closed form `heatKernel edgeAdj t = 1 + ((e^{-2t} - 1)/2) • L`
and scalar calculus only — `d/dt (e^{-2t} - 1)/2 |₀ = -1`, so the flow
`x + c(t) • (L *ᵥ x)` differentiates to `0 + (-1) • (L *ᵥ x) = ![2,-2]`.
Independent of the eigenbasis expansion, the entrywise derivative engine,
and `hasDerivAt_pi` — a wrong sign, factor, or eigenvalue anywhere in the
Phase C chain contradicts this computation (the closed form itself is the
independently QA'd `heatKernel_edge_closed_QA`, collapse-route). -/
theorem heatKernel_edge_deriv_raw_QA :
    HasDerivAt (fun t : ℝ => heatKernel edgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ))
      (![2, -2] : Fin 2 → ℝ) 0 := by
  have hact : ∀ t : ℝ, heatKernel edgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ)
      = (![1, 3] : Fin 2 → ℝ)
        + ((Real.exp (-(2 * t)) - 1) / 2) • (![ -2, 2] : Fin 2 → ℝ) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rw [heatKernel_zero, Matrix.one_mulVec]
      funext i
      fin_cases i <;> simp [smul_eq_mul]
    · rw [heatKernel_edge_closed_QA t ht, Matrix.add_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec_assoc, edgeLaplacian_mulVec_dc]
  rw [funext hact]
  have hc : HasDerivAt (fun t : ℝ => (Real.exp (-(2 * t)) - 1) / 2) (-1 : ℝ) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) 0 := by
      simpa using (hasDerivAt_id 0).const_mul (2 : ℝ)
    have h1 : HasDerivAt (fun t : ℝ => -(2 * t)) (-2 : ℝ) 0 := by
      simpa using h0.neg
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(2 * t))) (-2 : ℝ) 0 := by
      simpa using h1.exp
    have h3 : HasDerivAt (fun t : ℝ => Real.exp (-(2 * t)) - 1) (-2 : ℝ) 0 := by
      simpa using h2.sub (hasDerivAt_const 0 (1 : ℝ))
    simpa using h3.div_const 2
  have hsum := (hasDerivAt_const 0 (![1, 3] : Fin 2 → ℝ)).add
    (hc.smul_const (![ -2, 2] : Fin 2 → ℝ))
  convert hsum using 1
  funext i
  fin_cases i <;> simp

/-- **Infinitesimal mass conservation, theorem route**: the `onesVec` flow
differentiates at `t = 0` to `0` — the Phase C theorem at the conserved
vector, with the Laplacian kernel equation `laplacian_ones_in_kernel`
collapsing the derivative. The infinitesimal counterpart of Step 3's
`heatKernel_mulVec_onesVec`. -/
theorem heatKernel_edge_deriv_conservation_QA :
    HasDerivAt (fun t : ℝ => heatKernel edgeAdj t *ᵥ (onesVec : Fin 2 → ℝ)) 0 0 := by
  have h := heatKernel_mulVec_hasDerivAt_zero edgeAdj edgeAdj_isSymm onesVec
  rw [laplacian_ones_in_kernel] at h
  simpa using h

/-- **Infinitesimal mass conservation, conservation route**: the same
statement from Step 3 alone — the flow is *constantly* `onesVec`, so its
derivative is `0` with no eigenbasis, no expansion, and no Phase C input.
Two routes to one derivative; a Phase C defect at the kernel mode breaks
the theorem route but not this one. -/
theorem heatKernel_edge_deriv_conservation_route2_QA :
    HasDerivAt (fun t : ℝ => heatKernel edgeAdj t *ᵥ (onesVec : Fin 2 → ℝ)) 0 0 := by
  rw [funext fun t => heatKernel_mulVec_onesVec edgeAdj t]
  exact hasDerivAt_const 0 onesVec

/-!
## The first-order remainder bound (Phase C, Step 2)
-/

/-- The K₂ Laplacian's eigenvalues are nonnegative: PSD
(`laplacian_psd` at the nonnegative symmetric fixture) read at each
unit eigenvector through `quadForm_eigvecOf_self` — the per-index input
to the eigenvalue inventory below (independent of any sort machinery). -/
theorem edge_eigvalOf_nonneg (i : Fin 2) :
    0 ≤ eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i := by
  rw [← quadForm_eigvecOf_self (laplacian_symmetric edgeAdj edgeAdj_isSymm) i]
  exact laplacian_psd edgeAdj edgeAdj_isSymm edgeAdj_nonneg _

/-- The K₂ eigenvalues sum to the trace `2` (`eigvalOf_sum_eq_trace`
at the raw entrywise trace `edgeLaplacian_trace`). -/
theorem edge_eigvalOf_sum :
    ∑ i : Fin 2, eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i
      = 2 := by
  rw [eigvalOf_sum_eq_trace]
  exact edgeLaplacian_trace

/-- The K₂ eigenvalues multiply to the determinant `0`
(`det_eq_prod_eigenvalues` at the raw entrywise determinant
`edgeLaplacian_det`). -/
theorem edge_eigvalOf_prod :
    ∏ i : Fin 2, eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i
      = 0 := by
  have hd0 := (isHermitian_of_isSymm
    (laplacian_symmetric edgeAdj edgeAdj_isSymm)).det_eq_prod_eigenvalues
  rw [edgeLaplacian_det] at hd0
  exact hd0.symm

/-- **The K₂ eigenvalue inventory, per vertex index**: every `eigvalOf`
of the K₂ Laplacian is `0` or `2` — nonnegativity plus the trace sum
and the vanishing product (some factor is `0`; the other must be `2`)
— with both orderings covered. The per-index smallness window and the
eigen-sum constant below read their cases from here. -/
theorem edge_eigvalOf_cases (i : Fin 2) :
    eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i = 0
      ∨ eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i = 2 := by
  have hsum := edge_eigvalOf_sum
  have hprod := edge_eigvalOf_prod
  obtain ⟨j₀, -, hj₀⟩ := Finset.prod_eq_zero_iff.1 hprod
  rw [Fin.sum_univ_two] at hsum
  fin_cases j₀
  · have hz0 : eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) 0
        = 0 := hj₀
    have h1 : eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) 1
        = 2 := by
      have hn := edge_eigvalOf_nonneg 1
      linarith
    fin_cases i
    · exact Or.inl hz0
    · exact Or.inr h1
  · have hz1 : eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) 1
        = 0 := hj₀
    have h0 : eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) 0
        = 2 := by
      have hn := edge_eigvalOf_nonneg 0
      linarith
    fin_cases i
    · exact Or.inr h0
    · exact Or.inl hz1

/-- Some K₂ mode has eigenvalue exactly `2` (not both can be `0`: the
trace is `2`) — the index the window-fence witness below reads. -/
theorem edge_eigvalOf_exists_two :
    ∃ i : Fin 2, eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i
      = 2 := by
  by_contra hcon
  push_neg at hcon
  have h0 : ∀ i : Fin 2,
      eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i = 0 := by
    intro i
    rcases edge_eigvalOf_cases i with h | h
    · exact h
    · exact absurd h (hcon i)
  have hsum := edge_eigvalOf_sum
  rw [Fin.sum_univ_two, h0 0, h0 1] at hsum
  norm_num at hsum

/-- **The smallness window on K₂**: every time `s ∈ [0, 1/2]` meets the
remainder bound's hypothesis `|s · λᵢ| ≤ 1` (both inventory cases
compute: `|s · 0| = 0`, `|s · 2| = 2s ≤ 1`). The bound is usable on
exactly `[0, 1/2]` on this fixture — and provably not beyond (the fence
witness below). -/
theorem edge_window (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1/2) (i : Fin 2) :
    |s * eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i| ≤ 1 := by
  rcases edge_eigvalOf_cases i with h | h
  · rw [h, mul_zero, abs_zero]
    norm_num
  · rw [h, abs_of_nonneg (mul_nonneg hs0 zero_le_two), mul_comm]
    linarith

/-- The K₂ Laplacian's coordinate action, both entries — the raw input
to the mode-structure derivation below (rewritten on a fresh goal, so
the eigenbasis terms never sit under the literal). -/
theorem edgeLaplacian_mulVec_coords (v : Fin 2 → ℝ) :
    (laplacian edgeAdj *ᵥ v) 0 = v 0 - v 1
      ∧ (laplacian edgeAdj *ᵥ v) 1 = v 1 - v 0 := by
  rw [edgeLaplacian_eq]
  constructor <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two] <;> ring

/-- **The K₂ eigenmode structure**: every eigenvector of the nonzero
mode (eigenvalue `2`) is `c • ![1, -1]` with `2c² = 1` — the coordinate
eigen-equation (`v 1 = -v 0`) plus the unit normalization
(`eigvecOf_inner`). This is what makes the eigen-sum constant *exactly*
computable: the mode's contribution is `λ² |v ⬝ᵥ x| |v a| =
4 · 2|c| · |c| = 8c² = 4` regardless of the orientation sign `±`. -/
theorem edge_eigvecOf_mode_two {i : Fin 2}
    (hi : eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i = 2) :
    ∃ c : ℝ, eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i
        = c • (![1, -1] : Fin 2 → ℝ) ∧ 2 * c ^ 2 = 1 := by
  have hev : laplacian edgeAdj *ᵥ (eigvecOf (laplacian edgeAdj)
      (laplacian_symmetric edgeAdj edgeAdj_isSymm) i)
      = (2 : ℝ) • (eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) := by
    have h := (isHermitian_of_isSymm
      (laplacian_symmetric edgeAdj edgeAdj_isSymm)).mulVec_eigenvectorBasis i
    rw [show (isHermitian_of_isSymm
        (laplacian_symmetric edgeAdj edgeAdj_isSymm)).eigenvalues i
        = eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i from rfl,
      hi] at h
    exact h
  have hc := (edgeLaplacian_mulVec_coords (eigvecOf (laplacian edgeAdj)
    (laplacian_symmetric edgeAdj edgeAdj_isSymm) i)).1
  have hc' : (2 : ℝ) * (eigvecOf (laplacian edgeAdj)
        (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 0
      = (eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 0
        - (eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 1 := by
    rw [← hc, hev]
    simp
  have hne : (eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 1
      = -((eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 0) := by
    linarith
  refine ⟨(eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 0, ?_, ?_⟩
  · funext k
    fin_cases k <;> simp [hne]
  · have hu := eigvecOf_inner (laplacian edgeAdj)
      (laplacian_symmetric edgeAdj edgeAdj_isSymm) i i
    simp only [if_pos rfl, if_true] at hu
    rw [Fin.sum_univ_two] at hu
    have hv1 : (eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 1
          * (eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 1
        = (eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 0
          * (eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 0 := by
      rw [hne]; ring
    rw [pow_two]
    linarith

/-- The per-mode contribution at the λ = 2 mode: `4` exactly (the
mode-structure computation — `8c² = 4` at `2c² = 1`). -/
private theorem edge_remainder_somm (i : Fin 2) (h : eigvalOf (laplacian edgeAdj)
    (laplacian_symmetric edgeAdj edgeAdj_isSymm) i = 2) :
    (eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) ^ 2
      * |Matrix.dotProduct (eigvecOf (laplacian edgeAdj)
          (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) (![1, 3] : Fin 2 → ℝ)|
      * |(eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 0|
      = 4 := by
  obtain ⟨c, hc, hc2⟩ := edge_eigvecOf_mode_two h
  rw [h, hc]
  have hd : Matrix.dotProduct ((c • (![1, -1] : Fin 2 → ℝ))) (![1, 3] : Fin 2 → ℝ)
      = -(2 * c) := by
    simp [Matrix.dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring
  have h0 : ((c • (![1, -1] : Fin 2 → ℝ)) : Fin 2 → ℝ) 0 = c := by simp
  rw [hd, h0, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hcc : |c| * |c| = 1 / 2 := by
    have habs : |c| * |c| = c * c := by
      rw [← abs_mul, abs_of_nonneg (mul_self_nonneg c)]
    rw [habs]
    have h := hc2
    rw [pow_two] at h
    linarith
  have hf : (2 : ℝ) ^ 2 * (2 * |c|) * |c| = 4 := by
    have e1 : (2 * |c|) * |c| = 2 * (|c| * |c|) := by ring
    have e2 : (2 : ℝ) ^ 2 * (2 * |c|) * |c|
        = (2 : ℝ) ^ 2 * ((2 * |c|) * |c|) := by ring
    rw [e2, e1, hcc]
    norm_num
  exact hf

/-- **The eigen-sum constant on the fixture**: the remainder bound's
spectral constant at `x = ![1, 3]`, observable `a = 0` is exactly `4`
— the zero mode contributes `0`, the λ = 2 mode contributes `4`, and
the trace pins exactly one mode at each value. Load-bearing: this is
what turns the theorem's RHS into the concrete number `t² · 4` in the
witnesses below (a wrong eigenvalue or normalization in the shelf's
eigenbasis machinery would move it). -/
theorem edge_remainder_sum_eq :
    ∑ i : Fin 2, (eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) ^ 2
      * |Matrix.dotProduct (eigvecOf (laplacian edgeAdj)
          (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) (![1, 3] : Fin 2 → ℝ)|
      * |(eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i) 0|
      = 4 := by
  have hsum := edge_eigvalOf_sum
  rw [Fin.sum_univ_two] at hsum
  have hz : ∀ j : Fin 2, eigvalOf (laplacian edgeAdj)
        (laplacian_symmetric edgeAdj edgeAdj_isSymm) j = 0 →
      (eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) j) ^ 2
        * |Matrix.dotProduct (eigvecOf (laplacian edgeAdj)
            (laplacian_symmetric edgeAdj edgeAdj_isSymm) j) (![1, 3] : Fin 2 → ℝ)|
        * |(eigvecOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) j) 0|
      = 0 := by
    intro j hj
    rw [hj, zero_pow (by norm_num)]
    ring
  rcases edge_eigvalOf_cases 0 with e0 | e0 <;> rcases edge_eigvalOf_cases 1 with e1 | e1
  · rw [e0, e1] at hsum; norm_num at hsum
  · rw [Fin.sum_univ_two, hz 0 e0, edge_remainder_somm 1 e1]; norm_num
  · rw [Fin.sum_univ_two, edge_remainder_somm 0 e0, hz 1 e1]; norm_num
  · rw [e0, e1] at hsum; norm_num at hsum

/-- **The concrete-bound witness, theorem route**: at `t = 1/2` (the
window's endpoint) the first-order remainder at coordinate `0` of
`x = ![1, 3]` on K₂ is at most `1` — the Phase C theorem instantiated
with the window fact `edge_window`, the RHS eigen-sum evaluated to the
concrete `(1/2)² · 4 = 1` through `edge_remainder_sum_eq`. A wrong
constant anywhere in the theorem's `t²` or eigenvalue weights moves
this number. -/
theorem heatKernel_edge_remainder_bound_half_QA :
    |(heatKernel edgeAdj (1/2) *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      - (![1, 3] : Fin 2 → ℝ) 0
      + (1/2) * ((laplacian edgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)|
      ≤ 1 := by
  have h := heatKernel_firstOrder_remainder_apply_le edgeAdj edgeAdj_isSymm
    (![1, 3] : Fin 2 → ℝ) 0 (1/2) (edge_window (1/2) (by norm_num) (le_refl _))
  rw [edge_remainder_sum_eq] at h
  norm_num at h
  exact h

/-- **The raw remainder value, closed-form route** (at every nonzero
time): through the independently QA'd closed form
`heatKernel_edge_closed_QA` and hand arithmetic only — no eigenbasis,
no `Real.abs_exp_sub_one_sub_id_le` — the coordinate-`0` remainder of
`![1, 3]` on K₂ is exactly `1 - 2t - e^{-2t}`. The cross-check anchor:
at `t = 1/2` this is `-e⁻¹`, at `t = 1/4` it is `1/2 - e^{-1/2}`. -/
theorem heatKernel_edge_remainder_value_raw (t : ℝ) (ht : t ≠ 0) :
    (heatKernel edgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      - (![1, 3] : Fin 2 → ℝ) 0
      + t * ((laplacian edgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)
      = 1 - 2 * t - Real.exp (-(2 * t)) := by
  rw [heatKernel_edge_closed_QA t ht, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec_assoc, edgeLaplacian_mulVec_dc]
  norm_num [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The composite cross-check at `t = 1/2`**: raw value `-e⁻¹` (closed
form) inside the theorem's numeric bound `1` (eigen-sum route) —
`e⁻¹ ≤ 1`, both sides pinned by unrelated computations. A wrong sign,
factor, eigenvalue, or summation in either delivered chain (eigenbasis
expansion + termwise exponential bound vs. rank-one-idempotent closed
form) contradicts the other. -/
theorem heatKernel_edge_remainder_cross_QA : Real.exp (-1 : ℝ) ≤ 1 := by
  have h1 := heatKernel_edge_remainder_bound_half_QA
  have hval : (heatKernel edgeAdj (1/2) *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      - (![1, 3] : Fin 2 → ℝ) 0
      + (1/2) * ((laplacian edgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)
      = -(Real.exp (-1 : ℝ)) := by
    have h := heatKernel_edge_remainder_value_raw (1/2) (by norm_num)
    rw [h]
    norm_num
  rw [hval] at h1
  rwa [abs_neg, abs_of_nonneg (Real.exp_nonneg (-1))] at h1

/-- **The concrete bound at the interior point, interval route**: at
`t = 1/4` on the window `[0, 1/2]`, the interval-packaged theorem gives
the remainder bound `(1/4)² · 4 = 1/4` — the hypothesis-transfer step
(`|t·λ| ≤ |T·λ| ≤ 1` at `0 ≤ t ≤ T`) exercised at concrete numerics. -/
theorem heatKernel_edge_remainder_interval_QA :
    |(heatKernel edgeAdj (1/4) *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      - (![1, 3] : Fin 2 → ℝ) 0
      + (1/4) * ((laplacian edgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)|
      ≤ 1/4 := by
  have h := heatKernel_firstOrder_remainder_interval edgeAdj edgeAdj_isSymm
    (![1, 3] : Fin 2 → ℝ) 0 (T := 1/2) (t := 1/4)
    (edge_window (1/2) (by norm_num) (le_refl _)) (by norm_num) (by norm_num)
  rw [edge_remainder_sum_eq] at h
  norm_num at h
  exact h

/-- **The boundary-degradation witness**: the bound's constants at the
two times are `1` (at `t = 1/2`) and `1/4` (at `t = 1/4`) — halving the
time quarters the bound, the `t²` scaling made numeric on both sides:
each component is the *raw* closed-form remainder (`1/2 - e^{-1/2}` ≈
0.107 and `e⁻¹` ≈ 0.368) inside the *theorem-derived* bound. A wrong
power of `t` in the theorem (t¹ would give bounds `2` and `1/2`; t³
would give `1/2` and `1/16`) contradicts at least one component — the
"first-order" claim is thereby pinned as exactly quadratic, not
accidentally weaker or stronger. -/
theorem heatKernel_edge_remainder_degrades_QA :
    |(1/2 : ℝ) - Real.exp (-(1/2 : ℝ))| ≤ 1/4
      ∧ Real.exp (-(1 : ℝ)) ≤ 1 := by
  constructor
  · have hval := heatKernel_edge_remainder_value_raw (1/4) (by norm_num)
    have hbound := heatKernel_edge_remainder_interval_QA
    rw [hval] at hbound
    have harg : (2 : ℝ) * (1/4) = 1/2 := by norm_num
    rw [harg] at hbound
    have hnum : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    rw [hnum] at hbound
    exact hbound
  · exact heatKernel_edge_remainder_cross_QA

/-- **The window fence**: the smallness hypothesis provably *fails* at
`t = 1` on K₂ — some mode has `|1 · 2| = 2 ≰ 1`. The remainder bound is
genuinely local to `[0, 1/2]` on this fixture (usable exactly there per
`edge_window`), so the first-order claim is not accidentally global. -/
theorem heatKernel_edge_remainder_window_fenced_QA :
    ¬ ∀ i : Fin 2, |(1 : ℝ)
        * eigvalOf (laplacian edgeAdj) (laplacian_symmetric edgeAdj edgeAdj_isSymm) i| ≤ 1 := by
  intro h
  obtain ⟨i, hi⟩ := edge_eigvalOf_exists_two
  have h1 := h i
  rw [hi, one_mul] at h1
  norm_num at h1

end SpectralGraphTheory.QA
