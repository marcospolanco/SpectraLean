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
  pinning the `t²` scaling and the `t = 1/2` window fence); and the
  variance-decay section (2026-08-31,
  `proposals/heat-variance-decay.md`): exact attainment at Fiedler
  vectors on K₂ (`2 e^{-4t}`) and P₃ (`2 e^{-2t}`) at *every* time, the
  wrong-constant refutation, the λ₂ = 0 disconnected branch pinned exact
  (both sides `2/3`, the fixture's gap proved exactly zero), mean
  preservation by two independent routes, and the `t = 0` corner.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Heat
import Scaffold.QA.SpectralGraph.Poincare_QA
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Fixtures
-/

/-- Adjacency of the two-vertex complete graph `K₂`: symmetric, unit
weights, degrees (1, 1). -/
def heatEdgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

theorem heatEdgeAdj_isSymm : heatEdgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [heatEdgeAdj]

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
    heatKernel heatEdgeAdj 0 = !![1, 0; 0, 1] := by
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
theorem heatKernel_isSymm_edge_QA (t : ℝ) : (heatKernel heatEdgeAdj t).IsSymm :=
  heatKernel_isSymm heatEdgeAdj heatEdgeAdj_isSymm t

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
    heatKernel heatEdgeAdj 0 * heatKernel heatEdgeAdj t = heatKernel heatEdgeAdj t := by
  rw [heatKernel_mul_heatKernel, zero_add]

/-- …and `t = 0` on the right. -/
theorem heatKernel_semigroup_zero_right_QA (t : ℝ) :
    heatKernel heatEdgeAdj t * heatKernel heatEdgeAdj 0 = heatKernel heatEdgeAdj t := by
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
    heatKernel heatEdgeAdj t *ᵥ onesVec = onesVec :=
  heatKernel_mulVec_onesVec heatEdgeAdj t

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
theorem edgeLaplacian_eq : laplacian heatEdgeAdj = !![1, -1; -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, heatEdgeAdj, Fin.sum_univ_two]

/-- The K₂ Laplacian squares to twice itself: `!![1, -1; -1, 1]` squared
is `!![2, -2; -2, 2]`, all entries by literal arithmetic. This is the
`M * M = c • M` hypothesis of the Step-4 collapse — checked raw,
independent of any theorem. -/
theorem edgeLaplacian_mul_smul :
    laplacian heatEdgeAdj * laplacian heatEdgeAdj = 2 • laplacian heatEdgeAdj := by
  rw [edgeLaplacian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The K₂ Laplacian's hand eigenvector: `![1, -1]` has eigenvalue `2`
(`L *ᵥ ![1, -1] = ![2, -2] = 2 • ![1, -1]`), raw arithmetic — the
eigen-equation the mode-decay witnesses consume. -/
theorem edgeLaplacian_mulVec_mode :
    laplacian heatEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)
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
    laplacian heatEdgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ) = (![ -2, 2] : Fin 2 → ℝ) := by
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
    heatKernel heatEdgeAdj t
      = 1 + ((Real.exp (-(2 * t)) - 1) / 2) • laplacian heatEdgeAdj := by
  rw [heatKernel]
  have hM : (-(t • laplacian heatEdgeAdj)) * (-(t • laplacian heatEdgeAdj))
      = (-(2 * t)) • (-(t • laplacian heatEdgeAdj)) := by
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
    heatKernel heatEdgeAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)
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
    heatKernel heatEdgeAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)
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
theorem edgeLaplacian_trace : (laplacian heatEdgeAdj).trace = 2 := by
  simp [Matrix.trace, edgeLaplacian_eq, Fin.sum_univ_two]; norm_num

theorem edgeLaplacian_det : (laplacian heatEdgeAdj).det = 0 := by
  rw [edgeLaplacian_eq, Matrix.det_fin_two]
  norm_num

/-- **The K₂ Laplacian spectrum is `[0, 2]`**: sortedness plus trace
(`0 + 2 = 2`) and determinant (`0 * 2 = 0`) pin both entries — no axiom,
no spectral-theorem computation (the Cheeger QA pinning pattern, at the
combinatorial Laplacian). The two decay-factor QA theorems below read
their constants from here. -/
theorem edgeLaplacian_evals_QA :
    evals (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) ⟨0, by simp⟩ = 0 ∧
      evals (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) ⟨1, by simp⟩ = 2 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric heatEdgeAdj
          heatEdgeAdj_isSymm)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric heatEdgeAdj
          heatEdgeAdj_isSymm)).eigenvalues))).Sorted (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric heatEdgeAdj
          heatEdgeAdj_isSymm)).eigenvalues))).sum = 2 := by
    have htr : ∑ i : Fin 2, eigvalOf (laplacian heatEdgeAdj)
        (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i = 2 := by
      rw [eigvalOf_sum_eq_trace, edgeLaplacian_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric heatEdgeAdj
          heatEdgeAdj_isSymm)).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2, ((isHermitian_of_isSymm
        (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm (laplacian_symmetric heatEdgeAdj
        heatEdgeAdj_isSymm)).det_eq_prod_eigenvalues
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
  have h := heatKernel_decayFactor_antitone heatEdgeAdj heatEdgeAdj_isSymm
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

theorem heatEdgeAdj_nonneg : ∀ i j, 0 ≤ heatEdgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [heatEdgeAdj]

theorem edge_adj01 : (supportGraph heatEdgeAdj heatEdgeAdj_isSymm).Adj
    (0 : Fin 2) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [heatEdgeAdj]⟩

/-- The support graph of K₂ is connected (the single edge is a walk
between the two vertices). -/
theorem heatEdgeAdj_supportGraph_connected :
    (supportGraph heatEdgeAdj heatEdgeAdj_isSymm).Connected := by
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
    Filter.Tendsto (fun t : ℝ => heatKernel heatEdgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ))
      Filter.atTop (nhds (![2, 2] : Fin 2 → ℝ)) := by
  have h := heatKernel_mulVec_tendsto_atTop heatEdgeAdj heatEdgeAdj_isSymm
    heatEdgeAdj_nonneg heatEdgeAdj_supportGraph_connected (![1, 3] : Fin 2 → ℝ)
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
    Filter.Tendsto (fun t : ℝ => heatKernel heatEdgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ))
      Filter.atTop (nhds (![2, 2] : Fin 2 → ℝ)) := by
  have hev : ∀ t : ℝ, t ≠ 0 → heatKernel heatEdgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ)
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
        = heatKernel heatEdgeAdj 0 *ᵥ (![1, 3] : Fin 2 → ℝ)
    have h1 : heatKernel heatEdgeAdj 0 *ᵥ (![1, 3] : Fin 2 → ℝ)
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
    HasDerivAt (fun t : ℝ => heatKernel heatEdgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ))
      (![2, -2] : Fin 2 → ℝ) 0 := by
  have h := heatKernel_mulVec_hasDerivAt_zero heatEdgeAdj heatEdgeAdj_isSymm
    (![1, 3] : Fin 2 → ℝ)
  rw [edgeLaplacian_mulVec_dc] at h
  have hval : (-(![-2, 2] : Fin 2 → ℝ)) = ![2, -2] := by
    funext i
    fin_cases i <;> simp
  rw [hval] at h
  exact h

set_option linter.unnecessarySeqFocus false in
/-- **The derivative value on K₂, raw route**: the same statement through
the Step-4 closed form `heatKernel heatEdgeAdj t = 1 + ((e^{-2t} - 1)/2) • L`
and scalar calculus only — `d/dt (e^{-2t} - 1)/2 |₀ = -1`, so the flow
`x + c(t) • (L *ᵥ x)` differentiates to `0 + (-1) • (L *ᵥ x) = ![2,-2]`.
Independent of the eigenbasis expansion, the entrywise derivative engine,
and `hasDerivAt_pi` — a wrong sign, factor, or eigenvalue anywhere in the
Phase C chain contradicts this computation (the closed form itself is the
independently QA'd `heatKernel_edge_closed_QA`, collapse-route). -/
theorem heatKernel_edge_deriv_raw_QA :
    HasDerivAt (fun t : ℝ => heatKernel heatEdgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ))
      (![2, -2] : Fin 2 → ℝ) 0 := by
  have hact : ∀ t : ℝ, heatKernel heatEdgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ)
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
    HasDerivAt (fun t : ℝ => heatKernel heatEdgeAdj t *ᵥ (onesVec : Fin 2 → ℝ)) 0 0 := by
  have h := heatKernel_mulVec_hasDerivAt_zero heatEdgeAdj heatEdgeAdj_isSymm onesVec
  rw [laplacian_ones_in_kernel] at h
  simpa using h

/-- **Infinitesimal mass conservation, conservation route**: the same
statement from Step 3 alone — the flow is *constantly* `onesVec`, so its
derivative is `0` with no eigenbasis, no expansion, and no Phase C input.
Two routes to one derivative; a Phase C defect at the kernel mode breaks
the theorem route but not this one. -/
theorem heatKernel_edge_deriv_conservation_route2_QA :
    HasDerivAt (fun t : ℝ => heatKernel heatEdgeAdj t *ᵥ (onesVec : Fin 2 → ℝ)) 0 0 := by
  rw [funext fun t => heatKernel_mulVec_onesVec heatEdgeAdj t]
  exact hasDerivAt_const 0 onesVec

/-!
## The first-order remainder bound (Phase C, Step 2)
-/

/-- The K₂ Laplacian's eigenvalues are nonnegative: PSD
(`laplacian_psd` at the nonnegative symmetric fixture) read at each
unit eigenvector through `quadForm_eigvecOf_self` — the per-index input
to the eigenvalue inventory below (independent of any sort machinery). -/
theorem edge_eigvalOf_nonneg (i : Fin 2) :
    0 ≤ eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i := by
  rw [← quadForm_eigvecOf_self (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i]
  exact laplacian_psd heatEdgeAdj heatEdgeAdj_isSymm heatEdgeAdj_nonneg _

/-- The K₂ eigenvalues sum to the trace `2` (`eigvalOf_sum_eq_trace`
at the raw entrywise trace `edgeLaplacian_trace`). -/
theorem edge_eigvalOf_sum :
    ∑ i : Fin 2, eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i
      = 2 := by
  rw [eigvalOf_sum_eq_trace]
  exact edgeLaplacian_trace

/-- The K₂ eigenvalues multiply to the determinant `0`
(`det_eq_prod_eigenvalues` at the raw entrywise determinant
`edgeLaplacian_det`). -/
theorem edge_eigvalOf_prod :
    ∏ i : Fin 2, eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i
      = 0 := by
  have hd0 := (isHermitian_of_isSymm
    (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)).det_eq_prod_eigenvalues
  rw [edgeLaplacian_det] at hd0
  exact hd0.symm

/-- **The K₂ eigenvalue inventory, per vertex index**: every `eigvalOf`
of the K₂ Laplacian is `0` or `2` — nonnegativity plus the trace sum
and the vanishing product (some factor is `0`; the other must be `2`)
— with both orderings covered. The per-index smallness window and the
eigen-sum constant below read their cases from here. -/
theorem edge_eigvalOf_cases (i : Fin 2) :
    eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i = 0
      ∨ eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i = 2 := by
  have hsum := edge_eigvalOf_sum
  have hprod := edge_eigvalOf_prod
  obtain ⟨j₀, -, hj₀⟩ := Finset.prod_eq_zero_iff.1 hprod
  rw [Fin.sum_univ_two] at hsum
  fin_cases j₀
  · have hz0 : eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) 0
        = 0 := hj₀
    have h1 : eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) 1
        = 2 := by
      have hn := edge_eigvalOf_nonneg 1
      linarith
    fin_cases i
    · exact Or.inl hz0
    · exact Or.inr h1
  · have hz1 : eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) 1
        = 0 := hj₀
    have h0 : eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) 0
        = 2 := by
      have hn := edge_eigvalOf_nonneg 0
      linarith
    fin_cases i
    · exact Or.inr h0
    · exact Or.inl hz1

/-- Some K₂ mode has eigenvalue exactly `2` (not both can be `0`: the
trace is `2`) — the index the window-fence witness below reads. -/
theorem edge_eigvalOf_exists_two :
    ∃ i : Fin 2, eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i
      = 2 := by
  by_contra hcon
  push_neg at hcon
  have h0 : ∀ i : Fin 2,
      eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i = 0 := by
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
    |s * eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i| ≤ 1 := by
  rcases edge_eigvalOf_cases i with h | h
  · rw [h, mul_zero, abs_zero]
    norm_num
  · rw [h, abs_of_nonneg (mul_nonneg hs0 zero_le_two), mul_comm]
    linarith

/-- The K₂ Laplacian's coordinate action, both entries — the raw input
to the mode-structure derivation below (rewritten on a fresh goal, so
the eigenbasis terms never sit under the literal). -/
theorem edgeLaplacian_mulVec_coords (v : Fin 2 → ℝ) :
    (laplacian heatEdgeAdj *ᵥ v) 0 = v 0 - v 1
      ∧ (laplacian heatEdgeAdj *ᵥ v) 1 = v 1 - v 0 := by
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
    (hi : eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i = 2) :
    ∃ c : ℝ, eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i
        = c • (![1, -1] : Fin 2 → ℝ) ∧ 2 * c ^ 2 = 1 := by
  have hev : laplacian heatEdgeAdj *ᵥ (eigvecOf (laplacian heatEdgeAdj)
      (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i)
      = (2 : ℝ) • (eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) := by
    have h := (isHermitian_of_isSymm
      (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)).mulVec_eigenvectorBasis i
    rw [show (isHermitian_of_isSymm
        (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)).eigenvalues i
        = eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i from rfl,
      hi] at h
    exact h
  have hc := (edgeLaplacian_mulVec_coords (eigvecOf (laplacian heatEdgeAdj)
    (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i)).1
  have hc' : (2 : ℝ) * (eigvecOf (laplacian heatEdgeAdj)
        (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0
      = (eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0
        - (eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 1 := by
    rw [← hc, hev]
    simp
  have hne : (eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 1
      = -((eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0) := by
    linarith
  refine ⟨(eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0, ?_, ?_⟩
  · funext k
    fin_cases k <;> simp [hne]
  · have hu := eigvecOf_inner (laplacian heatEdgeAdj)
      (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i i
    simp only [if_pos rfl, if_true] at hu
    rw [Fin.sum_univ_two] at hu
    have hv1 : (eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 1
          * (eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 1
        = (eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0
          * (eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0 := by
      rw [hne]; ring
    rw [pow_two]
    linarith

/-- The per-mode contribution at the λ = 2 mode: `4` exactly (the
mode-structure computation — `8c² = 4` at `2c² = 1`). -/
private theorem edge_remainder_somm (i : Fin 2) (h : eigvalOf (laplacian heatEdgeAdj)
    (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i = 2) :
    (eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) ^ 2
      * |Matrix.dotProduct (eigvecOf (laplacian heatEdgeAdj)
          (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) (![1, 3] : Fin 2 → ℝ)|
      * |(eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0|
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
    ∑ i : Fin 2, (eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) ^ 2
      * |Matrix.dotProduct (eigvecOf (laplacian heatEdgeAdj)
          (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) (![1, 3] : Fin 2 → ℝ)|
      * |(eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0|
      = 4 := by
  have hsum := edge_eigvalOf_sum
  rw [Fin.sum_univ_two] at hsum
  have hz : ∀ j : Fin 2, eigvalOf (laplacian heatEdgeAdj)
        (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) j = 0 →
      (eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) j) ^ 2
        * |Matrix.dotProduct (eigvecOf (laplacian heatEdgeAdj)
            (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) j) (![1, 3] : Fin 2 → ℝ)|
        * |(eigvecOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) j) 0|
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
    |(heatKernel heatEdgeAdj (1/2) *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      - (![1, 3] : Fin 2 → ℝ) 0
      + (1/2) * ((laplacian heatEdgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)|
      ≤ 1 := by
  have h := heatKernel_firstOrder_remainder_apply_le heatEdgeAdj heatEdgeAdj_isSymm
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
    (heatKernel heatEdgeAdj t *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      - (![1, 3] : Fin 2 → ℝ) 0
      + t * ((laplacian heatEdgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)
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
  have hval : (heatKernel heatEdgeAdj (1/2) *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      - (![1, 3] : Fin 2 → ℝ) 0
      + (1/2) * ((laplacian heatEdgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)
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
    |(heatKernel heatEdgeAdj (1/4) *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      - (![1, 3] : Fin 2 → ℝ) 0
      + (1/4) * ((laplacian heatEdgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)|
      ≤ 1/4 := by
  have h := heatKernel_firstOrder_remainder_interval heatEdgeAdj heatEdgeAdj_isSymm
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
        * eigvalOf (laplacian heatEdgeAdj) (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i| ≤ 1 := by
  intro h
  obtain ⟨i, hi⟩ := edge_eigvalOf_exists_two
  have h1 := h i
  rw [hi, one_mul] at h1
  norm_num at h1


/-! ## Variance decay (QA layer) -/

theorem heatEdgeAdj_card : 2 ≤ Fintype.card (Fin 2) := le_refl 2

/-- **The K₂ exact-attainment pin**: at the Fiedler vector `![1, -1]`
the decayed variance is exactly `e^{-4t} · 2` at *every* `t ≥ 0` —
both sides of the theorem compute to the same closed form (the QA
shape a bound theorem can have at an eigenvector input). -/
theorem heat_variance_edge_attained_QA (t : ℝ) :
    (∑ i : Fin 2, ((heatKernel heatEdgeAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
          / (Fintype.card (Fin 2) : ℝ)) ^ 2)
      = Real.exp (-(4 * t)) * 2 := by
  have hmean : (∑ j : Fin 2, (![1, -1] : Fin 2 → ℝ) j)
      / (Fintype.card (Fin 2) : ℝ) = 0 := by
    norm_num [Fin.sum_univ_two, Fintype.card_fin, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  rw [heatKernel_edge_mode_engine_QA t, hmean]
  have hf : (Real.exp (-(2 * t))) ^ 2 = Real.exp (-(4 * t)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h0 : ((Real.exp (-(2 * t)) • (![1, -1] : Fin 2 → ℝ)) 0 - 0) ^ 2
      = (Real.exp (-(2 * t))) ^ 2 := by
    simp [Matrix.cons_val_zero]
  have h1 : ((Real.exp (-(2 * t)) • (![1, -1] : Fin 2 → ℝ)) 1 - 0) ^ 2
      = (Real.exp (-(2 * t))) ^ 2 := by
    simp [Matrix.cons_val_one, Matrix.head_cons]
  rw [Fin.sum_univ_two, h0, h1, hf]
  ring

/-- **The K₂ theorem instance**: the variance-decay theorem on the edge,
with the gap read from the independently pinned K₂ spectrum
(`edgeLaplacian_evals_QA`) — closing at `le_refl`, i.e. exact
attainment: no smaller constant than `e^{-2tλ₂}` works at the Fiedler
vector. -/
theorem heat_variance_edge_instance_QA (t : ℝ) (ht : 0 ≤ t) :
    (∑ i : Fin 2, ((heatKernel heatEdgeAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
          / (Fintype.card (Fin 2) : ℝ)) ^ 2)
      ≤ Real.exp (-(2 * t * secondEval (laplacian heatEdgeAdj)
          (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) heatEdgeAdj_card))
        * ∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
          - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
            / (Fintype.card (Fin 2) : ℝ)) ^ 2 :=
  heatKernel_variance_decay heatEdgeAdj heatEdgeAdj_isSymm heatEdgeAdj_nonneg
    heatEdgeAdj_card ht ![1, -1]

/-- The K₂ instance's RHS reads `e^{-4t} · 2` too: with the gap pinned
`2` and the Fiedler variance pinned `2`, the bound is *attained*, not
merely met. -/
theorem heat_variance_edge_bound_value_QA (t : ℝ) :
    Real.exp (-(2 * t * secondEval (laplacian heatEdgeAdj)
        (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) heatEdgeAdj_card))
      * ∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
          / (Fintype.card (Fin 2) : ℝ)) ^ 2
      = Real.exp (-(4 * t)) * 2 := by
  have h2 : secondEval (laplacian heatEdgeAdj)
      (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) heatEdgeAdj_card = 2 :=
    (edgeLaplacian_evals_QA).2
  have hvar : ∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
          / (Fintype.card (Fin 2) : ℝ)) ^ 2 = 2 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead,
      Fintype.card_fin]
    norm_num
  rw [h2, hvar]
  congr 1
  ring

/-- The P₃ Fiedler eigen-equation, raw entrywise: `L *ᵥ ![1, 0, -1] =
1 • ![1, 0, -1]` — the input the exponential eigenmode engine consumes
on the path fixture (independent of every theorem here). -/
theorem pcP3_laplacian_mulVec_fiedler :
    laplacian pcP3 *ᵥ (![1, 0, -1] : Fin 3 → ℝ)
      = (1 : ℝ) • (![1, 0, -1] : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply,
      Fin.sum_univ_three, laplacian, degreeMatrix, deg, pcP3]

/-- **The P₃ exact-attainment pin**: at the path's Fiedler vector the
decayed variance is exactly `e^{-2t} · 2` at every `t ≥ 0` — the same
attainment shape as K₂ at the *other* gap value (`1`, not `2`), on an
irregular-degree graph. -/
theorem heat_variance_p3_attained_QA (t : ℝ) :
    (∑ i : Fin 3, ((heatKernel pcP3 t *ᵥ (![1, 0, -1] : Fin 3 → ℝ)) i
        - (∑ j, (![1, 0, -1] : Fin 3 → ℝ) j)
          / (Fintype.card (Fin 3) : ℝ)) ^ 2)
      = Real.exp (-(2 * t)) * 2 := by
  have hmode : heatKernel pcP3 t *ᵥ (![1, 0, -1] : Fin 3 → ℝ)
      = Real.exp (-(t * 1)) • (![1, 0, -1] : Fin 3 → ℝ) := by
    rw [heatKernel]
    refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc,
      pcP3_laplacian_mulVec_fiedler, smul_smul, neg_smul]
  rw [hmode]
  have hmean : (∑ j : Fin 3, (![1, 0, -1] : Fin 3 → ℝ) j)
      / (Fintype.card (Fin 3) : ℝ) = 0 := by
    norm_num [Fin.sum_univ_three, Fintype.card_fin, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
  rw [hmean]
  have hf : (Real.exp (-(t * 1))) ^ 2 = Real.exp (-(2 * t)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h0 : ((Real.exp (-(t * 1)) • (![1, 0, -1] : Fin 3 → ℝ)) 0 - 0) ^ 2
      = (Real.exp (-(t * 1))) ^ 2 := by
    simp [Matrix.cons_val_zero]
  have h1 : ((Real.exp (-(t * 1)) • (![1, 0, -1] : Fin 3 → ℝ)) 1 - 0) ^ 2
      = 0 := by
    simp [Matrix.cons_val_one, Matrix.head_cons]
  have h2 : ((Real.exp (-(t * 1)) • (![1, 0, -1] : Fin 3 → ℝ)) 2 - 0) ^ 2
      = (Real.exp (-(t * 1))) ^ 2 := by
    simp [Matrix.cons_val_two, Matrix.head_cons]
  rw [Fin.sum_univ_three, h0, h1, h2, hf]
  ring

/-- **The P₃ theorem instance**: the variance-decay theorem on the path,
gap read from the pinned P₃ spectrum — again closing at an exact
attainment (`2 e^{-2t} = 2 e^{-2t}`). -/
theorem heat_variance_p3_instance_QA (t : ℝ) :
    (∑ i : Fin 3, ((heatKernel pcP3 t *ᵥ (![1, 0, -1] : Fin 3 → ℝ)) i
        - (∑ j, (![1, 0, -1] : Fin 3 → ℝ) j)
          / (Fintype.card (Fin 3) : ℝ)) ^ 2)
      = Real.exp (-(2 * t * secondEval (laplacian pcP3)
          (laplacian_symmetric pcP3 pcP3_isSymm) pcP3_card))
        * ∑ i : Fin 3, ((![1, 0, -1] : Fin 3 → ℝ) i
          - (∑ j, (![1, 0, -1] : Fin 3 → ℝ) j)
            / (Fintype.card (Fin 3) : ℝ)) ^ 2 := by
  have hvar : ∑ i : Fin 3, ((![1, 0, -1] : Fin 3 → ℝ) i
        - (∑ j, (![1, 0, -1] : Fin 3 → ℝ) j)
          / (Fintype.card (Fin 3) : ℝ)) ^ 2 = 2 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fintype.card_fin]
    norm_num
  rw [heat_variance_p3_attained_QA t, pcP3_secondEval_eq_one_QA, hvar]
  congr 1
  ring

/-- **The wrong-constant refutation**: replacing the gap `2` by `3` in
the K₂ instance makes the conclusion false at `t = 1` — the decayed
variance `2 e^{-4}` is *not* at most `2 e^{-6}` (since `e^{-6} <
e^{-4}`). The attained rate is load-bearing, not slack. -/
theorem heat_variance_edge_wrong_constant_refuted_QA :
    ¬ ((∑ i : Fin 2, ((heatKernel heatEdgeAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
          / (Fintype.card (Fin 2) : ℝ)) ^ 2)
        ≤ Real.exp (-(2 * (1 : ℝ) * 3))
          * ∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
            - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
              / (Fintype.card (Fin 2) : ℝ)) ^ 2) := by
  intro hcon
  have hval := heat_variance_edge_attained_QA 1
  have hvar : ∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
          / (Fintype.card (Fin 2) : ℝ)) ^ 2 = 2 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead,
      Fintype.card_fin]
    norm_num
  rw [hval, hvar, show -(4 * (1 : ℝ)) = -(4 : ℝ) by norm_num,
    show -(2 * (1 : ℝ) * 3) = -(6 : ℝ) by norm_num] at hcon
  have hlt : Real.exp (-(6 : ℝ)) < Real.exp (-(4 : ℝ)) :=
    Real.exp_lt_exp.mpr (by norm_num)
  linarith

/-- The disconnected `Fin 3` fixture is symmetric, nonnegative, and
card-eligible — the hypothesis set of the variance-decay theorem on
degenerate (zero-gap) input. -/
theorem disAdj_isSymm : disAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [disAdj]

theorem disAdj_nonneg : ∀ i j, 0 ≤ disAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [disAdj]

theorem disAdj_card : 2 ≤ Fintype.card (Fin 3) := by decide

/-- The component-signed vector `![1, 1, -2]` is `L`-harmonic on the
disconnected fixture, raw entrywise. -/
theorem disAdj_laplacian_mulVec_ker_QA :
    laplacian disAdj *ᵥ (![1, 1, -2] : Fin 3 → ℝ) = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply,
      Fin.sum_univ_three, laplacian, degreeMatrix, deg, disAdj]

/-- It is orthogonal to `onesVec` — so it is a *centered* kernel vector,
the witness that pins the fixture's gap to exactly zero. -/
theorem disAdj_ker_orth_QA :
    Matrix.dotProduct (![1, 1, -2] : Fin 3 → ℝ) onesVec = 0 := by
  simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_three]
  norm_num

/-- **The disconnected fixture's gap is exactly `0`**: at most `0` by the
Rayleigh bound at the centered kernel vector above, at least `0` by
sortedness (`evals ⟨0⟩ ≤ evals ⟨1⟩`) plus `laplacian_evals_zero`. This is
the λ₂ = 0 branch's fixture constant, pinned by hand. -/
theorem disAdj_secondEval_eq_zero_QA :
    secondEval (laplacian disAdj) (laplacian_symmetric disAdj disAdj_isSymm)
      disAdj_card = 0 := by
  have hx0 : (![1, 1, -2] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h2 : (![1, 1, -2] : Fin 3 → ℝ) 2 = 0 := congrFun h 2
    norm_num [Matrix.cons_val_two, Matrix.head_cons] at h2
  have hxorth := disAdj_ker_orth_QA
  have hR := secondEval_le_rayleigh (laplacian_symmetric disAdj disAdj_isSymm)
    (laplacian_psd disAdj disAdj_isSymm disAdj_nonneg)
    (laplacian_ones_in_kernel disAdj) disAdj_card hx0 hxorth
  rw [rayleigh, if_neg hx0, quadForm, disAdj_laplacian_mulVec_ker_QA,
    Matrix.dotProduct_zero, zero_div] at hR
  have hge : (0 : ℝ) ≤ secondEval (laplacian disAdj)
      (laplacian_symmetric disAdj disAdj_isSymm) disAdj_card := by
    have h0 : evals (laplacian_symmetric disAdj disAdj_isSymm)
        ⟨0, by simp⟩ = 0 :=
      laplacian_evals_zero disAdj disAdj_isSymm disAdj_nonneg (by simp)
    have hmono : evals (laplacian_symmetric disAdj disAdj_isSymm)
        ⟨0, by simp⟩
        ≤ evals (laplacian_symmetric disAdj disAdj_isSymm) ⟨1, by simp⟩ :=
      evals_sorted _ (Fin.le_def.2 zero_le_one)
    rw [show secondEval (laplacian disAdj)
          (laplacian_symmetric disAdj disAdj_isSymm) disAdj_card
        = evals (laplacian_symmetric disAdj disAdj_isSymm) ⟨1, by simp⟩ from rfl]
    exact h0 ▸ hmono
  linarith

/-- **The λ₂ = 0 branch is exact**: on the disconnected fixture, at the
component indicator (a kernel vector — heat fixes it by
`heatKernel_noLeakage_component_QA`), both sides of the variance decay
compute to exactly `2/3` at every time: the rate-`e^{0} = 1` bound is
*attained*, so the theorem's zero-gap branch is tight exactly where it
says nothing decays. -/
theorem heat_variance_disconn_attained_QA (t : ℝ) :
    (∑ i : Fin 3, ((heatKernel disAdj t *ᵥ
          (fun j => if j = 2 then (0 : ℝ) else 1)) i
        - (∑ j : Fin 3, (if j = 2 then (0 : ℝ) else 1))
          / (Fintype.card (Fin 3) : ℝ)) ^ 2)
      = 2 / 3
      ∧ Real.exp (-(2 * t * secondEval (laplacian disAdj)
          (laplacian_symmetric disAdj disAdj_isSymm) disAdj_card))
          * ∑ i : Fin 3, ((if (i : Fin 3) = 2 then (0 : ℝ) else 1)
            - (∑ j : Fin 3, (if j = 2 then (0 : ℝ) else 1))
              / (Fintype.card (Fin 3) : ℝ)) ^ 2
        = 2 / 3 := by
  have hfix := heatKernel_noLeakage_component_QA t
  have hsum : (∑ j : Fin 3, (if j = 2 then (0 : ℝ) else 1)) = 2 := by
    have e0 : (if (0 : Fin 3) = 2 then (0 : ℝ) else 1) = 1 :=
      if_neg (by decide)
    have e1 : (if (1 : Fin 3) = 2 then (0 : ℝ) else 1) = 1 :=
      if_neg (by decide)
    have e2 : (if (2 : Fin 3) = 2 then (0 : ℝ) else 1) = 0 :=
      if_pos rfl
    rw [Fin.sum_univ_three, e0, e1, e2]
    norm_num
  have hmean : (∑ j : Fin 3, (if j = 2 then (0 : ℝ) else 1))
      / (Fintype.card (Fin 3) : ℝ) = 2 / 3 := by
    rw [hsum, Fintype.card_fin]
    norm_num
  have hvar : ∑ i : Fin 3, ((if (i : Fin 3) = 2 then (0 : ℝ) else 1)
      - 2 / 3) ^ 2 = 2 / 3 := by
    have e0 : ((if (0 : Fin 3) = 2 then (0 : ℝ) else 1) - 2 / 3) ^ 2
        = 1 / 9 := by
      rw [if_neg (by decide)]
      norm_num
    have e1 : ((if (1 : Fin 3) = 2 then (0 : ℝ) else 1) - 2 / 3) ^ 2
        = 1 / 9 := by
      rw [if_neg (by decide)]
      norm_num
    have e2 : ((if (2 : Fin 3) = 2 then (0 : ℝ) else 1) - 2 / 3) ^ 2
        = 4 / 9 := by
      rw [if_pos rfl]
      norm_num
    rw [Fin.sum_univ_three, e0, e1, e2]
    norm_num
  constructor
  · rw [hfix, hmean]
    exact hvar
  · rw [hmean, hvar, disAdj_secondEval_eq_zero_QA, mul_zero, neg_zero,
      Real.exp_zero, one_mul]

/-- The theorem instance on the disconnected fixture — the λ₂ = 0 branch
exercised end to end, closing at equality by the pin above. -/
theorem heat_variance_disconn_instance_QA (t : ℝ) (ht : 0 ≤ t) :
    (∑ i : Fin 3, ((heatKernel disAdj t *ᵥ
          (fun j => if j = 2 then (0 : ℝ) else 1)) i
        - (∑ j : Fin 3, (if j = 2 then (0 : ℝ) else 1))
          / (Fintype.card (Fin 3) : ℝ)) ^ 2)
      ≤ Real.exp (-(2 * t * secondEval (laplacian disAdj)
          (laplacian_symmetric disAdj disAdj_isSymm) disAdj_card))
        * ∑ i : Fin 3, ((if (i : Fin 3) = 2 then (0 : ℝ) else 1)
          - (∑ j : Fin 3, (if j = 2 then (0 : ℝ) else 1))
            / (Fintype.card (Fin 3) : ℝ)) ^ 2 :=
  heatKernel_variance_decay disAdj disAdj_isSymm disAdj_nonneg
    disAdj_card ht _

/-- **Mean preservation, theorem route**: the total mass of the heat flow
of `![1, 3]` on `K₂` at `t = 1` is exactly the input mass `4` —
`sum_heatKernel_mulVec` instantiated on the fixture (a transpose slip in
the lemma's symmetry transfer would move this number). -/
theorem heat_variance_mean_preserved_theorem_QA :
    ∑ i : Fin 2, (heatKernel heatEdgeAdj 1 *ᵥ (![1, 3] : Fin 2 → ℝ)) i = 4 := by
  rw [sum_heatKernel_mulVec heatEdgeAdj heatEdgeAdj_isSymm 1 (![1, 3] : Fin 2 → ℝ)]
  norm_num [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

set_option linter.unnecessarySeqFocus false in
/-- **Mean preservation, raw route**: the same mass `4` from the closed
form `heatKernel heatEdgeAdj 1 = 1 + ((e^{-2} - 1)/2) • L` and hand
arithmetic (`![1,3] + c • ![-2, 2]` sums to `4 + c · 0`) — independent
of the symmetry-transfer lemma. Two routes to one mass. -/
theorem heat_variance_mean_preserved_raw_QA :
    ∑ i : Fin 2, (heatKernel heatEdgeAdj 1 *ᵥ (![1, 3] : Fin 2 → ℝ)) i = 4 := by
  rw [heatKernel_edge_closed_QA 1 (by norm_num), Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec_assoc, edgeLaplacian_mulVec_dc]
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- **The `t = 0` corner**: at time zero the statement is the identity
`Var(f) ≤ 1 · Var(f)` — instantiated at every input on the fixture, with
the rate factor computing to `exp 0 = 1` by hand. -/
theorem heat_variance_zero_time_QA (f : Fin 2 → ℝ) :
    (∑ i : Fin 2, ((heatKernel heatEdgeAdj 0 *ᵥ f) i
        - (∑ j, f j) / (Fintype.card (Fin 2) : ℝ)) ^ 2)
      = ∑ i : Fin 2, (f i
          - (∑ j, f j) / (Fintype.card (Fin 2) : ℝ)) ^ 2 := by
  rw [heatKernel_zero, Matrix.one_mulVec]

/-!
## Adversarial fences over the heat family (2026-09-05)

`proposals/adversarial-fences-heat-family.md`: the audit method's
eighteenth application — 30 hypothesis-form fences over the shelf's
unfenced clause surface (the exponential engines' `hM` clauses, the
rank-one collapse's `hc`/`hM`, the decay factors' `ht`/`hij`/`hnonneg`,
the DC limit's `hconn`/`hnonneg`, both variance-decay twins'
`hnn`/`ht`, the normalized/walk conservation-and-conjugation `hd`
clauses, and the eigenvalue-plumbing `hnn`/`hμ`), at four new fixtures
(`hfNegAdj`, `hfZeroAdj`, `hfRegAdj`, `hfAsymAdj`, `hfNz`) plus the
delivered `heatEdgeAdj`/`disAdj` pins. Every declaration is a fence (the
dropped-hypothesis statement refuted at a fixture where every kept
hypothesis is genuine) or its fixture-pin/isolation companion; nothing
here touches an axiom.
-/

section HeatFences

/-! ### Numeric helpers -/

/-- The `9/4 ≤ e` pin: two applications of `add_one_le_exp` at `1/2`
composed through `exp_add`. Every exponential fence constant below
(`e ≠ 1`, `e ≠ 2`, `e⁴ > 21`) reads from this one bound. -/
theorem hf_exp_one_ge : (9 / 4 : ℝ) ≤ Real.exp 1 := by
  have h1 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
  have h1' : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have h := Real.add_one_le_exp (1 / 2 : ℝ)
    norm_num at h
    exact h
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; ring_nf
  have h3 : ((3 / 2 : ℝ) * (3 / 2 : ℝ)) ≤ Real.exp (1 / 2) * Real.exp (1 / 2) :=
    mul_le_mul h1' h1' (by norm_num) (Real.exp_nonneg _)
  have h4 : (3 / 2 : ℝ) * (3 / 2 : ℝ) = 9 / 4 := by norm_num
  rw [h4, h2] at h3
  exact h3

theorem hf_exp_one_ne_two : Real.exp 1 ≠ 2 := by
  intro h
  have := hf_exp_one_ge
  rw [h] at this
  norm_num at this

theorem hf_exp_one_ne_one : Real.exp 1 ≠ 1 := by
  intro h
  have := hf_exp_one_ge
  rw [h] at this
  norm_num at this

theorem hf_exp_two_gt_one : (1 : ℝ) < Real.exp 2 :=
  Real.one_lt_exp_iff.2 (by norm_num)

theorem hf_exp_four_gt_one : (1 : ℝ) < Real.exp 4 :=
  Real.one_lt_exp_iff.2 (by norm_num)

/-- The `e⁴ > 21` fence constant: `(9/4)⁴ = 6561/256 > 21`. -/
theorem hf_exp_four_gt_21 : (21 : ℝ) < Real.exp 4 := by
  have h1 : ((9 / 4 : ℝ)) ^ 4 ≤ (Real.exp 1) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hf_exp_one_ge 4
  have h2 : ((9 / 4 : ℝ)) ^ 4 = 6561 / 256 := by norm_num
  rw [h2] at h1
  have h4 : (Real.exp 1) ^ 4 = Real.exp 4 := by
    have := Real.exp_nat_mul 1 4
    rw [Nat.cast_ofNat] at this
    rw [← this]
    congr 1
    norm_num
  rw [h4] at h1
  have h3 : (21 : ℝ) < 6561 / 256 := by norm_num
  linarith

theorem hf_exp_neg_one_ne_one : Real.exp (-1 : ℝ) ≠ 1 := by
  intro h
  have hlt : Real.exp (-1 : ℝ) < Real.exp (0 : ℝ) := Real.exp_lt_exp.2 (by norm_num)
  rw [Real.exp_zero, h] at hlt
  norm_num at hlt

theorem hf_exp_neg_three_ne_one : Real.exp (-3 : ℝ) ≠ 1 := by
  intro h
  have hlt : Real.exp (-3 : ℝ) < Real.exp (0 : ℝ) := Real.exp_lt_exp.2 (by norm_num)
  rw [Real.exp_zero, h] at hlt
  norm_num at hlt

theorem hf_sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  intro h
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h, mul_zero] at h2
  norm_num at h2

/-! ### α — the general exponential engines -/

/-- The scalar-matrix exponential at the identity: `exp 1 = e • 1`
through the delivered scalar-collapse engine. -/
theorem hf_exp_one_matrix : NormedSpace.exp ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ)
    = Real.exp 1 • 1 := by
  have h := matrix_exp_smul_one (V := Fin 2) (1 : ℝ)
  rw [one_smul] at h
  exact h

/-- The scalar-matrix exponential at the negated identity. -/
theorem hf_exp_neg_one_matrix : NormedSpace.exp ℝ (-(1 : Matrix (Fin 2) (Fin 2) ℝ))
    = Real.exp (-1 : ℝ) • 1 := by
  have hneg : -(1 : Matrix (Fin 2) (Fin 2) ℝ) = (-1 : ℝ) • 1 :=
    (neg_one_smul ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ)).symm
  rw [hneg]
  exact matrix_exp_smul_one (V := Fin 2) (-1)

/-- **Fence (`hM` of `exp_eq_one_add_of_mul_self_eq_zero`)**: at the
identity matrix the dropped statement `exp 1 = 1 + 1` is refuted
through the scalar-matrix exponential and `9/4 ≤ e`. First negative
witness for the clause anywhere in the repository. -/
theorem hf_sqzero_M_fence :
    ¬ (NormedSpace.exp ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = 1 + (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro h
  rw [hf_exp_one_matrix] at h
  have h00 := congrFun (congrFun h 0) 0
  simp at h00
  exact hf_exp_one_ne_two (by linarith)

/-- **Fence (`hM` of `exp_neg_smul_eq_one_add_of_mul_self_eq_zero`)**:
at the identity matrix and `t = 1` the dropped statement's two sides
are `e⁻¹ • 1` and `1 − 1 = 0`. -/
theorem hf_neg_smul_M_fence :
    ¬ (NormedSpace.exp ℝ (-(1 • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      = 1 + -(1 • (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [one_smul] at h00
  rw [hf_exp_neg_one_matrix] at h00
  norm_num at h00

/-- **Fence (`hM` of `pow_mulVec_smul`)**: at the zero matrix,
`v = ![1, 0]`, `μ = 1`, `n = 1`, the dropped statement reads
`0 = ![1, 0]`. -/
theorem hf_pow_mulVec_fence :
    ¬ ((0 : Matrix (Fin 2) (Fin 2) ℝ) ^ 1 *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (1 : ℝ) ^ 1 • (![1, 0] : Fin 2 → ℝ)) := by
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- **Fence (`hM` of `exp_mulVec_eq_smul_of_mulVec_eq_smul`)**: at the
zero matrix, `v = ![1, 0]`, `μ = 1`, the eigenmode engine's dropped
statement reads `v = e • v`. -/
theorem hf_engine_M_fence :
    ¬ ((NormedSpace.exp ℝ (0 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = Real.exp 1 • (![1, 0] : Fin 2 → ℝ)) := by
  intro h
  rw [NormedSpace.exp_zero, Matrix.one_mulVec] at h
  have h0 := congrFun h 0
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h0
  exact hf_exp_one_ne_one h0.symm

/-- **Fence (`hM` of `exp_mulVec_eq_of_mulVec_eq_zero`)**: at the
identity matrix and `v = ![1, 0]` (a *non*-kernel vector: `1 *ᵥ v =
v ≠ 0`), the dropped statement reads `e • v = v`. -/
theorem hf_kernel_M_fence :
    ¬ ((NormedSpace.exp ℝ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (![1, 0] : Fin 2 → ℝ)) := by
  intro h
  rw [hf_exp_one_matrix, Matrix.smul_mulVec_assoc, Matrix.one_mulVec] at h
  have h0 := congrFun h 0
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h0
  exact hf_exp_one_ne_one h0

/-- **Fence (`hμ` of `tendsto_exp_neg_mul_atTop`)**: at `μ = 0` the
mode factor is the constant `1` and does not tend to `0`. -/
theorem hf_tendsto_mu_fence :
    ¬ Filter.Tendsto (fun t : ℝ => Real.exp (-(t * 0))) Filter.atTop (nhds 0) := by
  have hconst : (fun t : ℝ => Real.exp (-(t * 0))) = fun _ : ℝ => (1 : ℝ) := by
    funext t; simp
  rw [hconst]
  intro h
  have h1 := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at h1

/-! ### β — the nilpotent fixture and the rank-one-idempotent collapse -/

/-- The nilpotent fixture: `hfNz² = 0` with `hfNz ≠ 0` — the square-zero
collapse applies genuinely while the rank-one clause `M * M = 1 • M`
genuinely fails (`0 ≠ hfNz`). -/
def hfNz : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

theorem hfNz_mul_hfNz : hfNz * hfNz = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hfNz]

theorem hfNz_ne_zero : hfNz ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [hfNz] at h01

theorem hfNz_exp_eq : NormedSpace.exp ℝ hfNz = 1 + hfNz :=
  exp_eq_one_add_of_mul_self_eq_zero _ hfNz_mul_hfNz

/-- **Fence (`hc` of `exp_eq_one_add_of_mul_self_eq_smul`)**: at `c = 0`
with the hypothesis `hfNz² = 0 • hfNz` genuinely satisfiable, the
dropped statement's coefficient `(e⁰ − 1)/0` is *junk zero*, collapsing
the claim to `exp hfNz = 1` — refuted by the square-zero collapse at
the nonzero fixture. The junk-division corner class. -/
theorem hf_collapse_c_fence :
    ¬ (NormedSpace.exp ℝ hfNz = 1 + ((Real.exp 0 - 1) / 0) • hfNz) := by
  intro h
  rw [hfNz_exp_eq, Real.exp_zero, sub_self, div_zero, zero_smul, add_zero] at h
  have h01 := congrFun (congrFun h 0) 1
  simp [hfNz] at h01

/-- **Fence (`hM` of `exp_eq_one_add_of_mul_self_eq_smul`)**: at
`c = 1` (genuine) with `hfNz² = 0 ≠ 1 • hfNz` genuinely failing, the
dropped statement reads `1 + hfNz = 1 + (e − 1) • hfNz` — i.e. `e = 2`
entrywise. -/
theorem hf_collapse_M_fence :
    ¬ (NormedSpace.exp ℝ hfNz = 1 + ((Real.exp 1 - 1) / 1) • hfNz) := by
  intro h
  rw [hfNz_exp_eq, div_one] at h
  have h01 := congrFun (congrFun h 0) 1
  simp only [Matrix.add_apply, Matrix.one_apply, hfNz, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, zero_add] at h01
  norm_num at h01
  exact hf_exp_one_ne_two (by linarith)

/-! ### γ — K₂ decay-factor fences -/

/-- **Fence (`ht` of `heatKernel_decayFactor_antitone`)**: at `t = -1`
(beyond the semigroup's forward window) the monotonicity claim flips to
`e² ≤ e⁰ = 1`. -/
theorem hf_antitone_t_fence :
    ¬ (Real.exp (-((-1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)
          ⟨1, by simp⟩))
      ≤ Real.exp (-((-1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)
          ⟨0, by simp⟩))) := by
  rw [(edgeLaplacian_evals_QA).2, (edgeLaplacian_evals_QA).1]
  rw [show (-1 : ℝ) * 2 = -2 by norm_num, show (-1 : ℝ) * 0 = 0 by norm_num,
    neg_neg, neg_zero, Real.exp_zero]
  exact not_le.2 hf_exp_two_gt_one

/-- **Fence (`hij` of `heatKernel_decayFactor_antitone`)**: with the
index order genuinely violated (`⟨1⟩ ≤ ⟨0⟩` false), the claim reads
`e⁰ = 1 ≤ e⁻²`. -/
theorem hf_antitone_ij_fence :
    ¬ (Real.exp (-((1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)
          ⟨0, by simp⟩))
      ≤ Real.exp (-((1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)
          ⟨1, by simp⟩))) := by
  rw [(edgeLaplacian_evals_QA).1, (edgeLaplacian_evals_QA).2]
  rw [show (1 : ℝ) * 0 = 0 by norm_num, show (1 : ℝ) * 2 = 2 by norm_num,
    neg_zero, Real.exp_zero]
  have hlt : Real.exp (-(2 : ℝ)) < 1 := by
    have := Real.exp_lt_exp.2 (by norm_num : (-(2 : ℝ)) < 0)
    rwa [Real.exp_zero] at this
  exact not_le.2 hlt

/-- **Fence (`ht` of `heatKernel_decayFactor_le_one`)**: at `t = -1` the
top mode's factor is `e² > 1` — dissipation genuinely needs forward
time. -/
theorem hf_le_one_t_fence :
    ¬ (Real.exp (-((-1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm)
          ⟨1, by simp⟩)) ≤ 1) := by
  rw [(edgeLaplacian_evals_QA).2, show (-1 : ℝ) * 2 = -2 by norm_num, neg_neg]
  exact not_le.2 hf_exp_two_gt_one

/-! ### δ — the negative-edge fixture `hfNegAdj` -/

/-- The negative edge: symmetric, degrees `(-2, -2)`, Laplacian
`!![-2, 2; 2, -2]]` with spectrum `[-4, 0]` — the signed fixture
carrying the dissipation-failure witnesses. -/
def hfNegAdj : Matrix (Fin 2) (Fin 2) ℝ := !![0, -2; -2, 0]

theorem hfNegAdj_isSymm : hfNegAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [hfNegAdj]

/-- Isolation: the nonnegativity clause genuinely fails at the
off-diagonal `-2`. -/
theorem hfNegAdj_not_nonneg : ¬ ∀ i j, 0 ≤ hfNegAdj i j := by
  intro h
  have h01 := h 0 1
  simp only [hfNegAdj, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h01
  norm_num at h01

theorem hfNegAdj_deg (i : Fin 2) : deg hfNegAdj i = -2 := by
  fin_cases i <;> simp [deg, hfNegAdj, Fin.sum_univ_two]

theorem hfNegAdj_laplacian : laplacian hfNegAdj = !![-2, 2; 2, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, hfNegAdj, Fin.sum_univ_two]

theorem hfNegAdj_laplacian_trace : (laplacian hfNegAdj).trace = -4 := by
  simp [Matrix.trace, hfNegAdj_laplacian, Fin.sum_univ_two]; norm_num

theorem hfNegAdj_laplacian_det : (laplacian hfNegAdj).det = 0 := by
  rw [hfNegAdj_laplacian, Matrix.det_fin_two]; norm_num

theorem hfNegAdj_card : 2 ≤ Fintype.card (Fin 2) := le_refl 2

/-- Length-two list identification (local twin of the delivered
`list_two_eq`). -/
private theorem hf_list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- Two-point spectrum pinning, negative-sum variant: a sorted
length-two list with sum `-4` and product `0` is `[-4, 0]`. -/
private theorem hf_two_point_pin_neg {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = -4)
    (hprod : l.prod = 0) :
    l.get ⟨0, by omega⟩ = -4 ∧ l.get ⟨1, by omega⟩ = 0 := by
  obtain ⟨g₀, g₁, hg⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, hf_list_two_eq h2⟩
  subst hg
  have hmono : g₀ ≤ g₁ := hs.rel_get_of_lt (show (0 : Fin 2) < 1 by decide)
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with h0 | h1
  · exfalso
    subst h0
    linarith
  · subst h1
    refine ⟨?_, ?_⟩
    · have h0 : g₀ = -4 := by linarith
      simpa using h0
    · simp

/-- **The negative-edge Laplacian spectrum is `[-4, 0]`** — the
two-point pattern (sortedness + trace `-4` + determinant `0`) at the
signed fixture. Four fences below read their constants from here. -/
theorem hfNegAdj_laplacian_evals_QA :
    evals (laplacian_symmetric hfNegAdj hfNegAdj_isSymm) ⟨0, by simp⟩ = -4 ∧
      evals (laplacian_symmetric hfNegAdj hfNegAdj_isSymm) ⟨1, by simp⟩ = 0 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric hfNegAdj
          hfNegAdj_isSymm)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric hfNegAdj
          hfNegAdj_isSymm)).eigenvalues))).Sorted (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric hfNegAdj
          hfNegAdj_isSymm)).eigenvalues))).sum = -4 := by
    have htr : ∑ i : Fin 2, eigvalOf (laplacian hfNegAdj)
        (laplacian_symmetric hfNegAdj hfNegAdj_isSymm) i = -4 := by
      rw [eigvalOf_sum_eq_trace, hfNegAdj_laplacian_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (laplacian_symmetric hfNegAdj
          hfNegAdj_isSymm)).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2, ((isHermitian_of_isSymm
        (laplacian_symmetric hfNegAdj hfNegAdj_isSymm)).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm
        (laplacian_symmetric hfNegAdj hfNegAdj_isSymm)).det_eq_prod_eigenvalues
      rw [hfNegAdj_laplacian_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact hf_two_point_pin_neg hlen hsorted hsum hprod

theorem hfNegAdj_secondEval_eq_zero :
    secondEval (laplacian hfNegAdj) (laplacian_symmetric hfNegAdj hfNegAdj_isSymm)
      hfNegAdj_card = 0 :=
  hfNegAdj_laplacian_evals_QA.2

theorem hfNegAdj_laplacian_mulVec_mode :
    laplacian hfNegAdj *ᵥ (![1, -1] : Fin 2 → ℝ)
      = (-4 : ℝ) • (![1, -1] : Fin 2 → ℝ) := by
  rw [hfNegAdj_laplacian]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, smul_eq_mul] <;>
    norm_num

theorem hfNegAdj_heatKernel_mode (t : ℝ) :
    heatKernel hfNegAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp (4 * t) • (![1, -1] : Fin 2 → ℝ) := by
  rw [heatKernel]
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, hfNegAdj_laplacian_mulVec_mode,
    smul_smul, ← neg_smul]
  congr 2
  ring

/-- **Fence (`hnonneg` of `heatKernel_decayFactor_le_one`)**: on the
signed fixture the bottom mode's "decay" factor is `e⁴ > 1` —
dissipation fails on signed input. First negative witness for the
clause. -/
theorem hf_le_one_nn_fence :
    ¬ (Real.exp (-((1 : ℝ) * evals (laplacian_symmetric hfNegAdj hfNegAdj_isSymm)
          ⟨0, by simp⟩)) ≤ 1) := by
  rw [hfNegAdj_laplacian_evals_QA.1, show (1 : ℝ) * (-4) = -4 by norm_num, neg_neg]
  exact not_le.2 hf_exp_four_gt_one

/-- **Fence (`hnonneg` of `heatKernel_mulVec_tendsto_atTop`)**: the
alternating mode's flow is `e^{4t} • ![1, -1]` — coordinate `0` is
bounded below by `1`, so the flow does not tend to the claimed mean
`0`. The DC limit genuinely needs nonnegative input: on signed input
modes grow instead of dissipating. -/
theorem hf_dc_nn_fence :
    ¬ Filter.Tendsto (fun t : ℝ => heatKernel hfNegAdj t *ᵥ (![1, -1] : Fin 2 → ℝ))
      Filter.atTop
      (nhds (((∑ j, (![1, -1] : Fin 2 → ℝ) j) / (Fintype.card (Fin 2) : ℝ))
        • (onesVec : Fin 2 → ℝ))) := by
  have hmean : ((∑ j, (![1, -1] : Fin 2 → ℝ) j) / (Fintype.card (Fin 2) : ℝ))
      • (onesVec : Fin 2 → ℝ) = 0 := by
    have hsum : (∑ j, (![1, -1] : Fin 2 → ℝ) j) = 0 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      norm_num
    rw [hsum, zero_div, zero_smul]
  rw [hmean]
  intro h
  have h0 : Filter.Tendsto
      (fun t : ℝ => (heatKernel hfNegAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)) 0)
      Filter.atTop (nhds 0) := by
    have hpi := (tendsto_pi_nhds.1 h) 0
    simpa using hpi
  have hmode0 : ∀ t : ℝ, (heatKernel hfNegAdj t *ᵥ (![1, -1] : Fin 2 → ℝ)) 0
      = Real.exp (4 * t) := by
    intro t
    rw [hfNegAdj_heatKernel_mode t]
    simp
  rw [funext hmode0] at h0
  have hmem : (Set.Iio (1 / 2 : ℝ)) ∈ nhds (0 : ℝ) :=
    isOpen_Iio.mem_nhds (by norm_num)
  have h1 := h0 hmem
  obtain ⟨b, hb⟩ := mem_atTop_sets.1 h1
  have hmax : (0 : ℝ) ≤ max b 0 := le_max_right b 0
  have hge : (1 : ℝ) ≤ Real.exp (4 * max b 0) := by
    have h4 : Real.exp (0 : ℝ) ≤ Real.exp (4 * max b 0) :=
      Real.exp_le_exp.2 (mul_nonneg (by norm_num) hmax)
    rwa [Real.exp_zero] at h4
  have hlt : Real.exp (4 * max b 0) < 1 / 2 := hb (max b 0) (le_max_left b 0)
  linarith

/-- **Fence (`hnn` of `heatKernel_variance_decay`)**: at the signed
fixture, `t = 1`, the Fiedler input `![1, -1]` (mean `0`) has output
variance `2e⁸` against the rate-`e⁰ = 1` bound on input variance `2` —
the variance bound genuinely needs PSD. -/
theorem hf_var_nn_fence :
    ¬ (∑ i : Fin 2, ((heatKernel hfNegAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j) / (Fintype.card (Fin 2) : ℝ)) ^ 2
      ≤ Real.exp (-(2 * (1 : ℝ) * secondEval (laplacian hfNegAdj)
          (laplacian_symmetric hfNegAdj hfNegAdj_isSymm) hfNegAdj_card))
        * ∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
          - (∑ j, (![1, -1] : Fin 2 → ℝ) j) / (Fintype.card (Fin 2) : ℝ)) ^ 2) := by
  have hmean : (∑ j, (![1, -1] : Fin 2 → ℝ) j) / (Fintype.card (Fin 2) : ℝ) = 0 := by
    have hsum : (∑ j, (![1, -1] : Fin 2 → ℝ) j) = 0 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      norm_num
    rw [hsum, zero_div]
  have hvar : ∑ i : Fin 2, (![1, -1] : Fin 2 → ℝ) i ^ 2 = 2 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Fin.sum_univ_two]
    norm_num
  rw [hfNegAdj_secondEval_eq_zero, hmean]
  simp only [sub_zero]
  rw [hfNegAdj_heatKernel_mode 1]
  have hout : ∑ i : Fin 2, ((Real.exp (4 * (1 : ℝ)) • (![1, -1] : Fin 2 → ℝ)) i) ^ 2
      = 2 * (Real.exp 4) ^ 2 := by
    have e0 : (((Real.exp (4 * (1 : ℝ)) • (![1, -1] : Fin 2 → ℝ)) : Fin 2 → ℝ) 0) ^ 2
        = (Real.exp 4) ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one]
    have e1 : (((Real.exp (4 * (1 : ℝ)) • (![1, -1] : Fin 2 → ℝ)) : Fin 2 → ℝ) 1) ^ 2
        = (Real.exp 4) ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons]
      ring_nf
    rw [Fin.sum_univ_two, e0, e1]
    ring
  rw [hout, hvar, show 2 * (1 : ℝ) * 0 = 0 by norm_num, neg_zero, Real.exp_zero, one_mul]
  intro hle
  have hgt : (1 : ℝ) < (Real.exp 4) ^ 2 := by
    nlinarith [hf_exp_four_gt_one, Real.exp_nonneg 4]
  linarith

/-- **Fence (`hnn` of `secondEval_le_eigvalOf_of_ne_zero`)**: at the
index carrying the eigenvalue `-4` (from `evals_mem_eigvalOf` at the
pinned bottom entry), the claim reads `λ₂ = 0 ≤ -4`. Below-gap
eigenvalues are only kernel eigenvalues on PSD input. -/
theorem hf_secondEval_nn_fence :
    ∃ i : Fin 2, eigvalOf (laplacian hfNegAdj)
        (laplacian_symmetric hfNegAdj hfNegAdj_isSymm) i ≠ 0 ∧
      ¬ (secondEval (laplacian hfNegAdj)
          (laplacian_symmetric hfNegAdj hfNegAdj_isSymm) hfNegAdj_card
        ≤ eigvalOf (laplacian hfNegAdj)
            (laplacian_symmetric hfNegAdj hfNegAdj_isSymm) i) := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric hfNegAdj hfNegAdj_isSymm) ⟨0, by simp⟩
  rw [hfNegAdj_laplacian_evals_QA.1] at hi
  refine ⟨i, ?_, ?_⟩
  · rw [← hi]; norm_num
  · rw [hfNegAdj_secondEval_eq_zero, ← hi]; norm_num

/-- Junk-`√` pin: at the negative degrees both diagonal entries of
`degreeSqrt` are zero (`√(-2) = 0`), so the whole matrix vanishes. -/
theorem hfNegAdj_degreeSqrt_eq_zero : degreeSqrt hfNegAdj = 0 := by
  ext i j
  simp only [degreeSqrt, Matrix.diagonal_apply, Matrix.zero_apply]
  by_cases h : i = j
  · rw [if_pos h, hfNegAdj_deg, Real.sqrt_eq_zero']
    norm_num
  · rw [if_neg h]

/-- **Fence (`hd` of `sum_deg_mul_sq_eq`)**: at the negative edge the
degree-weighted sum is `-2` while the `√D`-conjugate pairing is junk
(`√(-2) = 0` on both coordinates). -/
theorem hf_pi_fence :
    ¬ (∑ i : Fin 2, deg hfNegAdj i * ((![1, 0] : Fin 2 → ℝ) i * (![1, 0] : Fin 2 → ℝ) i)
      = Matrix.dotProduct (degreeSqrt hfNegAdj *ᵥ (![1, 0] : Fin 2 → ℝ))
          (degreeSqrt hfNegAdj *ᵥ (![1, 0] : Fin 2 → ℝ))) := by
  intro h
  have hL : ∑ i : Fin 2, deg hfNegAdj i * ((![1, 0] : Fin 2 → ℝ) i * (![1, 0] : Fin 2 → ℝ) i)
      = -2 := by
    have e0 : deg hfNegAdj 0 * ((![1, 0] : Fin 2 → ℝ) 0 * (![1, 0] : Fin 2 → ℝ) 0) = -2 := by
      simp only [Matrix.cons_val_zero, Matrix.head_cons]
      rw [hfNegAdj_deg 0]
      norm_num
    have e1 : deg hfNegAdj 1 * ((![1, 0] : Fin 2 → ℝ) 1 * (![1, 0] : Fin 2 → ℝ) 1) = 0 := by
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail]
      rw [hfNegAdj_deg 1]
      norm_num
    rw [Fin.sum_univ_two, e0, e1]
    norm_num
  rw [hL, hfNegAdj_degreeSqrt_eq_zero] at h
  simp only [Matrix.zero_mulVec, Matrix.dotProduct_zero] at h
  norm_num at h

/-- **Fence (`hd` of `sum_deg_mul_eq`)**: the cross-term twin at the
same fixture — `-2 ≠ 0`. -/
theorem hf_pi_cross_fence :
    ¬ (∑ i : Fin 2, deg hfNegAdj i * (![1, 0] : Fin 2 → ℝ) i
      = Matrix.dotProduct (degreeSqrt hfNegAdj *ᵥ (onesVec : Fin 2 → ℝ))
          (degreeSqrt hfNegAdj *ᵥ (![1, 0] : Fin 2 → ℝ))) := by
  intro h
  have hL : ∑ i : Fin 2, deg hfNegAdj i * (![1, 0] : Fin 2 → ℝ) i = -2 := by
    have e0 : deg hfNegAdj 0 * (![1, 0] : Fin 2 → ℝ) 0 = -2 := by
      simp only [Matrix.cons_val_zero, Matrix.head_cons]
      rw [hfNegAdj_deg 0]
      norm_num
    have e1 : deg hfNegAdj 1 * (![1, 0] : Fin 2 → ℝ) 1 = 0 := by
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail]
      rw [hfNegAdj_deg 1]
      norm_num
    rw [Fin.sum_univ_two, e0, e1]
    norm_num
  rw [hL, hfNegAdj_degreeSqrt_eq_zero] at h
  simp only [Matrix.zero_mulVec, Matrix.dotProduct_zero] at h
  norm_num at h

/-! ### ε — the disconnected fixture (delivered pins reused) -/

/-- The `{0, 1}`-edge's antisymmetric mode is an eigenvector at `2` on
the delivered disconnected fixture — the eigen-equation the
backward-time fence consumes. -/
theorem disAdj_laplacian_mulVec_mode :
    laplacian disAdj *ᵥ (![1, -1, 0] : Fin 3 → ℝ)
      = (2 : ℝ) • (![1, -1, 0] : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply, Fin.sum_univ_three,
      laplacian, degreeMatrix, deg, disAdj] <;>
    norm_num

theorem disAdj_heatKernel_minus_one_mode :
    heatKernel disAdj (-1) *ᵥ (![1, -1, 0] : Fin 3 → ℝ)
      = Real.exp 2 • (![1, -1, 0] : Fin 3 → ℝ) := by
  rw [heatKernel]
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  rw [neg_smul, neg_neg, one_smul, disAdj_laplacian_mulVec_mode]

/-- **Fence (`hconn` of `heatKernel_mulVec_tendsto_atTop`)**: at the
isolated vertex's indicator the flow is *constant* (the delivered
`heatKernel_isolated_fixed_QA`), so it converges to the indicator —
which is not the global mean `(1/3) • onesVec`. The DC limit genuinely
needs connectivity. -/
theorem hf_dc_conn_fence :
    ¬ Filter.Tendsto
        (fun t : ℝ => heatKernel disAdj t *ᵥ (fun j => if j = 2 then (1 : ℝ) else 0))
        Filter.atTop
        (nhds (((∑ j : Fin 3, (if j = 2 then (1 : ℝ) else 0))
            / (Fintype.card (Fin 3) : ℝ)) • (onesVec : Fin 3 → ℝ))) := by
  intro h
  rw [funext (heatKernel_isolated_fixed_QA)] at h
  have hc := tendsto_nhds_unique h tendsto_const_nhds
  have e2 := congrFun hc 2
  have hsum : (∑ j : Fin 3, (if j = 2 then (1 : ℝ) else 0)) = 1 := by
    have e0 : (if (0 : Fin 3) = 2 then (1 : ℝ) else 0) = 0 := if_neg (by decide)
    have e1 : (if (1 : Fin 3) = 2 then (1 : ℝ) else 0) = 0 := if_neg (by decide)
    have e2' : (if (2 : Fin 3) = 2 then (1 : ℝ) else 0) = 1 := if_pos rfl
    rw [Fin.sum_univ_three, e0, e1, e2']
    norm_num
  simp only [hsum, Fintype.card_fin, onesVec, Pi.smul_apply, smul_eq_mul, mul_one,
    if_pos rfl] at e2
  norm_num at e2

/-- **Fence (`ht` of `heatKernel_variance_decay`)**: at `t = -1` the
backward flow grows the eigenvalue-`2` mode — output variance `2e⁴`
against the rate-`e⁰ = 1` bound on input variance `2`. Negative time
is the backward (growth) semigroup, and the variance bound genuinely
excludes it. -/
theorem hf_var_t_fence :
    ¬ (∑ i : Fin 3, ((heatKernel disAdj (-1) *ᵥ (![1, -1, 0] : Fin 3 → ℝ)) i
        - (∑ j, (![1, -1, 0] : Fin 3 → ℝ) j) / (Fintype.card (Fin 3) : ℝ)) ^ 2
      ≤ Real.exp (-(2 * (-1 : ℝ) * secondEval (laplacian disAdj)
          (laplacian_symmetric disAdj disAdj_isSymm) disAdj_card))
        * ∑ i : Fin 3, ((![1, -1, 0] : Fin 3 → ℝ) i
          - (∑ j, (![1, -1, 0] : Fin 3 → ℝ) j) / (Fintype.card (Fin 3) : ℝ)) ^ 2) := by
  have hmean : (∑ j, (![1, -1, 0] : Fin 3 → ℝ) j) / (Fintype.card (Fin 3) : ℝ) = 0 := by
    have hsum : (∑ j, (![1, -1, 0] : Fin 3 → ℝ) j) = 0 := by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons]
      norm_num
    rw [hsum, zero_div]
  have hvar : ∑ i : Fin 3, (![1, -1, 0] : Fin 3 → ℝ) i ^ 2 = 2 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Fin.sum_univ_three]
    norm_num
  rw [hmean, disAdj_heatKernel_minus_one_mode]
  simp only [sub_zero]
  have hout : ∑ i : Fin 3, ((Real.exp 2 • (![1, -1, 0] : Fin 3 → ℝ)) i) ^ 2
      = 2 * (Real.exp 2) ^ 2 := by
    have e0 : (((Real.exp 2 • (![1, -1, 0] : Fin 3 → ℝ)) : Fin 3 → ℝ) 0) ^ 2
        = (Real.exp 2) ^ 2 := by
      simp [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    have e1 : (((Real.exp 2 • (![1, -1, 0] : Fin 3 → ℝ)) : Fin 3 → ℝ) 1) ^ 2
        = (Real.exp 2) ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons]
      ring
    have e2 : (((Real.exp 2 • (![1, -1, 0] : Fin 3 → ℝ)) : Fin 3 → ℝ) 2) ^ 2 = 0 := by
      simp [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.head_cons]
    rw [Fin.sum_univ_three, e0, e1, e2]
    ring
  rw [hout, hvar, disAdj_secondEval_eq_zero_QA,
    show 2 * (-1 : ℝ) * 0 = 0 by norm_num, neg_zero, Real.exp_zero, one_mul]
  intro hle
  have hgt : (1 : ℝ) < (Real.exp 2) ^ 2 := by
    nlinarith [hf_exp_two_gt_one, Real.exp_nonneg 2]
  linarith

/-! ### ζ — the asymmetric mass fixture `hfAsymAdj` -/

/-- The asymmetric fixture: degrees `(2, 1)`, Laplacian
`!![2, -2; -1, 1]]` with square `3 • L` — the mass-preservation fence's
carrier. -/
def hfAsymAdj : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 1, 0]

theorem hfAsymAdj_not_isSymm : ¬ hfAsymAdj.IsSymm := by
  intro h
  have h01 := Matrix.IsSymm.apply h 0 1
  simp only [hfAsymAdj, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h01
  norm_num at h01

theorem hfAsymAdj_laplacian : laplacian hfAsymAdj = !![2, -2; -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, hfAsymAdj, Fin.sum_univ_two]

theorem hfAsymAdj_laplacian_sq :
    laplacian hfAsymAdj * laplacian hfAsymAdj = (3 : ℝ) • laplacian hfAsymAdj := by
  rw [hfAsymAdj_laplacian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, smul_eq_mul, Fin.sum_univ_two] <;> ring

theorem hfAsymAdj_laplacian_mulVec_e0 :
    laplacian hfAsymAdj *ᵥ (![1, 0] : Fin 2 → ℝ) = (![2, -1] : Fin 2 → ℝ) := by
  rw [hfAsymAdj_laplacian]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

theorem hfAsymAdj_heatKernel_one :
    heatKernel hfAsymAdj 1 *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (![1, 0] : Fin 2 → ℝ) - ((1 - Real.exp (-3)) / 3) • (![2, -1] : Fin 2 → ℝ) := by
  have hM : (-(laplacian hfAsymAdj)) * (-(laplacian hfAsymAdj))
      = (-3 : ℝ) • (-(laplacian hfAsymAdj)) := by
    rw [neg_mul_neg, hfAsymAdj_laplacian_sq,
      ← neg_one_smul ℝ (laplacian hfAsymAdj), smul_smul]
    congr 1
    norm_num
  have hc : (-3 : ℝ) ≠ 0 := by norm_num
  have hexp := exp_eq_one_add_of_mul_self_eq_smul (-(laplacian hfAsymAdj)) hc hM
  rw [heatKernel]
  simp only [one_smul]
  rw [hexp, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.neg_mulVec, hfAsymAdj_laplacian_mulVec_e0]
  have hcoe : ((Real.exp (-3) - 1) / (-3 : ℝ)) • (-(![2, -1] : Fin 2 → ℝ))
      = -(((1 - Real.exp (-3)) / 3) • (![2, -1] : Fin 2 → ℝ)) := by
    have h0 : (Real.exp (-3) - 1) / (-3 : ℝ) = (1 - Real.exp (-3)) / 3 := by
      ring_nf
    rw [h0]
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
  rw [hcoe]
  funext i
  fin_cases i <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] <;>
    ring

/-- **Fence (`hA` of `sum_heatKernel_mulVec`)**: on the asymmetric
fixture the flow of `![1, 0]` at `t = 1` has mass `1 - α` with
`α = (1 - e⁻³)/3 ≠ 0` — mean preservation genuinely needs symmetry. -/
theorem hf_sum_hA_fence :
    ¬ (∑ i : Fin 2, (heatKernel hfAsymAdj 1 *ᵥ (![1, 0] : Fin 2 → ℝ)) i
      = ∑ j, (![1, 0] : Fin 2 → ℝ) j) := by
  intro h
  rw [hfAsymAdj_heatKernel_one] at h
  have hα : (1 - Real.exp (-3)) / 3 ≠ 0 := by
    intro h0
    have h1 : 1 - Real.exp (-3) = 0 := by
      have h2 : 3 * ((1 - Real.exp (-3)) / 3) = 3 * 0 := by rw [h0]
      linarith
    exact hf_exp_neg_three_ne_one (by linarith)
  have hsum : ∀ α : ℝ,
      ∑ i : Fin 2, ((![1, 0] : Fin 2 → ℝ) - α • (![2, -1] : Fin 2 → ℝ)) i = 1 - α := by
    intro α
    simp [Fin.sum_univ_two]
    ring
  have hsumin : (∑ j, (![1, 0] : Fin 2 → ℝ) j) = 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead]
    norm_num
  rw [hsum, hsumin] at h
  exact hα (by linarith)

/-! ### η — K₂ kernel-mode and remainder-window fences -/

/-- **Fence (`hμ` of `eigvecOf_ker_eq_smul_onesVec_of_secondEval_pos`)**:
at the index carrying the eigenvalue `2`, the mode-structure pin
(`eigvecOf i = c • ![1, -1]` with `2c² = 1`) contradicts the
kernel-mode claim `= d • onesVec` (which would force `c = 0`). The
clause genuinely excludes nonzero modes, with the gap positivity (and
every other hypothesis) genuine at K₂. -/
theorem hf_ker_mode_fence :
    ∃ i : Fin 2, eigvalOf (laplacian heatEdgeAdj)
        (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i ≠ 0 ∧
      ¬ (∃ c : ℝ, eigvecOf (laplacian heatEdgeAdj)
          (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i
        = c • (onesVec : Fin 2 → ℝ)) := by
  obtain ⟨i, hi⟩ := edge_eigvalOf_exists_two
  obtain ⟨c, hc, hc2⟩ := edge_eigvecOf_mode_two hi
  refine ⟨i, by rw [hi]; norm_num, ?_⟩
  intro ⟨d, hd⟩
  have hcd : c • (![1, -1] : Fin 2 → ℝ) = d • (onesVec : Fin 2 → ℝ) :=
    hc.symm.trans hd
  have e0 : c = d := by
    have h := congrFun hcd 0
    simpa [onesVec, Matrix.cons_val_zero] using h
  have e1 : -c = d := by
    have h := congrFun hcd 1
    simpa [onesVec, Matrix.cons_val_one, Matrix.head_cons] using h
  have hc0 : c = 0 := by linarith
  rw [hc0] at hc2
  norm_num at hc2

/-- Isolation: the gap positivity is genuine at K₂ (`λ₂ = 2 > 0`,
read from the delivered spectrum pin). -/
theorem hf_edge_gap_pos :
    0 < secondEval (laplacian heatEdgeAdj)
      (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) heatEdgeAdj_card := by
  have h2 : secondEval (laplacian heatEdgeAdj)
      (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) heatEdgeAdj_card = 2 :=
    (edgeLaplacian_evals_QA).2
  rw [h2]
  norm_num

/-- **Fence (`ht` of `heatKernel_firstOrder_remainder_apply_le`)**: at
`t = -2` (window genuinely failing: `|{-2} · 2| = 4 ≰ 1`), the raw
remainder is `e⁴ - 5 > 16` against the eigen-sum constant `4 · t² =
16` — the smallness window is genuinely load-bearing. -/
theorem hf_remainder_t_fence :
    ¬ (|(heatKernel heatEdgeAdj (-2) *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
       - (![1, 3] : Fin 2 → ℝ) 0
       + (-2) * ((laplacian heatEdgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0)|
      ≤ (-2 : ℝ) ^ 2 * ∑ i : Fin 2, (eigvalOf (laplacian heatEdgeAdj)
          (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) ^ 2
        * |Matrix.dotProduct (eigvecOf (laplacian heatEdgeAdj)
            (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) (![1, 3] : Fin 2 → ℝ)|
        * |(eigvecOf (laplacian heatEdgeAdj)
            (laplacian_symmetric heatEdgeAdj heatEdgeAdj_isSymm) i) 0|) := by
  rw [edge_remainder_sum_eq, show (-2 : ℝ) ^ 2 = 4 by norm_num]
  have hflow : (heatKernel heatEdgeAdj (-2) *ᵥ (![1, 3] : Fin 2 → ℝ)) 0
      = 2 - Real.exp 4 := by
    have hc := heatKernel_edge_closed_QA (-2) (by norm_num)
    rw [hc, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
      edgeLaplacian_mulVec_dc]
    have he : -(2 * (-2 : ℝ)) = 4 := by norm_num
    rw [he]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.head_cons]
    have hd : ((Real.exp 4 - 1) / 2) * (-2) = -(Real.exp 4 - 1) := by
      ring_nf
    rw [hd]
    ring
  have hx0 : (![1, 3] : Fin 2 → ℝ) 0 = 1 := by simp
  have hL0 : (laplacian heatEdgeAdj *ᵥ (![1, 3] : Fin 2 → ℝ)) 0 = -2 := by
    rw [edgeLaplacian_mulVec_dc]; simp
  rw [hflow, hx0, hL0]
  have heq : (2 - Real.exp 4) - 1 + (-2 : ℝ) * (-2) = 5 - Real.exp 4 := by ring
  rw [heq]
  have hgt := hf_exp_four_gt_21
  have habs : |(5 : ℝ) - Real.exp 4| = Real.exp 4 - 5 := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [habs]
  norm_num
  exact hgt

/-! ### θ — the zero-degree signed fixture `hfZeroAdj` -/

/-- The zero-degree signed fixture: degrees `(0, 2)`, so the
`degreeInvSqrt` congruence junk-kills to the zero matrix
(`normalizedLaplacian = 1`) while `walkLaplacian = !![1, 0; -1, 1]]`
survives with its asymmetric row — both heat kernels evaluate in
closed form. -/
def hfZeroAdj : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 2; 2, 0]

theorem hfZeroAdj_isSymm : hfZeroAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [hfZeroAdj]

theorem hfZeroAdj_deg_zero : deg hfZeroAdj 0 = 0 := by
  simp [deg, hfZeroAdj, Fin.sum_univ_two]

theorem hfZeroAdj_deg_one : deg hfZeroAdj 1 = 2 := by
  simp [deg, hfZeroAdj, Fin.sum_univ_two]

/-- Isolation: the positive-degree clause genuinely fails at vertex
`0`. -/
theorem hfZeroAdj_not_hd : ¬ ∀ i, 0 < deg hfZeroAdj i := by
  intro h
  have h0 := h 0
  rw [hfZeroAdj_deg_zero] at h0
  norm_num at h0

theorem hfZeroAdj_congruence_zero :
    degreeInvSqrt hfZeroAdj * hfZeroAdj * degreeInvSqrt hfZeroAdj = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply, deg, hfZeroAdj,
      Real.sqrt_zero, inv_zero, Fin.sum_univ_two]

theorem hfZeroAdj_normalizedLaplacian : normalizedLaplacian hfZeroAdj = 1 := by
  rw [normalizedLaplacian, hfZeroAdj_congruence_zero, sub_zero]

theorem hfZeroAdj_walkLaplacian : walkLaplacian hfZeroAdj = !![1, 0; -1, 1] := by
  rw [walkLaplacian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.one_apply, walkTransitionMatrix_apply, deg,
      hfZeroAdj, Fin.sum_univ_two, inv_zero]

theorem hfZeroAdj_walkHeatKernel_one :
    walkHeatKernel hfZeroAdj 1 = Real.exp (-1 : ℝ) • !![1, 0; 1, 1] := by
  have hNsq : (walkLaplacian hfZeroAdj - 1) * (walkLaplacian hfZeroAdj - 1) = 0 := by
    rw [hfZeroAdj_walkLaplacian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two]
  have hsplit : -((1 : ℝ) • walkLaplacian hfZeroAdj)
      = (-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + (-((1 : ℝ) • (walkLaplacian hfZeroAdj - 1))) := by
    ext i j
    simp only [one_smul]
    by_cases h : i = j
    · simp [Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply, Matrix.sub_apply,
        Pi.smul_apply, smul_eq_mul, h]
      ring
    · simp [Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply, Matrix.sub_apply,
        Pi.smul_apply, smul_eq_mul, h]
  have hcomm : Commute ((-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (-((1 : ℝ) • (walkLaplacian hfZeroAdj - 1))) := by
    show ((-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        * (-((1 : ℝ) • (walkLaplacian hfZeroAdj - 1)))
      = (-((1 : ℝ) • (walkLaplacian hfZeroAdj - 1)))
        * ((-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  have hNexp : NormedSpace.exp ℝ (-((1 : ℝ) • (walkLaplacian hfZeroAdj - 1)))
      = 1 + (-((1 : ℝ) • (walkLaplacian hfZeroAdj - 1))) :=
    exp_neg_smul_eq_one_add_of_mul_self_eq_zero _ hNsq 1
  rw [walkHeatKernel, hsplit, Matrix.exp_add_of_commute ℝ _ _ hcomm,
    matrix_exp_smul_one (V := Fin 2), hNexp, Matrix.smul_mul, Matrix.one_mul]
  congr 1
  simp only [one_smul, hfZeroAdj_walkLaplacian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply, Matrix.one_apply,
      if_true, ite_true] <;>
    norm_num

theorem hfZeroAdj_degreeSqrt_onesVec :
    degreeSqrt hfZeroAdj *ᵥ (onesVec : Fin 2 → ℝ) = ![0, Real.sqrt 2] := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, degreeSqrt, Matrix.diagonal_apply,
      hfZeroAdj_deg_zero, hfZeroAdj_deg_one, onesVec, Fin.sum_univ_two, Real.sqrt_zero]

/-- **Fence (`hd` of `normalizedHeatKernel_mulVec_degreeSqrt_onesVec`)**:
at the zero-degree signed fixture the normalized flow of `√D · 1` is
`e⁻¹ (0, √2) ≠ (0, √2)` — the normalized mass-conservation twin
genuinely needs positive degrees. -/
theorem hf_norm_heat_hd_fence :
    ¬ (normalizedHeatKernel hfZeroAdj 1 *ᵥ (degreeSqrt hfZeroAdj *ᵥ (onesVec : Fin 2 → ℝ))
      = degreeSqrt hfZeroAdj *ᵥ (onesVec : Fin 2 → ℝ)) := by
  rw [hfZeroAdj_degreeSqrt_onesVec]
  have hker : normalizedHeatKernel hfZeroAdj 1 = Real.exp (-1 : ℝ) • 1 := by
    rw [normalizedHeatKernel, hfZeroAdj_normalizedLaplacian, one_smul]
    exact hf_exp_neg_one_matrix
  rw [hker, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  intro h
  have e1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_zero] at e1
  rcases mul_eq_zero.1 (show (Real.exp (-1) - 1) * Real.sqrt 2 = 0 by
      have h2 : (Real.exp (-1) - 1) * Real.sqrt 2
          = Real.exp (-1) * Real.sqrt 2 - Real.sqrt 2 := by ring
      rw [h2, sub_eq_zero_of_eq (by linarith)]) with hm | hs
  · exact hf_exp_neg_one_ne_one (by linarith)
  · exact hf_sqrt_two_ne_zero hs

/-- **Fence (`hd` of `walkHeatKernel_mulVec_onesVec`)**: the walk flow of
`onesVec` is `e⁻¹ (1, 2) ≠ (1, 1)`. -/
theorem hf_walk_heat_hd_fence :
    ¬ (walkHeatKernel hfZeroAdj 1 *ᵥ (onesVec : Fin 2 → ℝ)
      = (onesVec : Fin 2 → ℝ)) := by
  intro h
  rw [hfZeroAdj_walkHeatKernel_one, Matrix.smul_mulVec_assoc] at h
  have hflow : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (onesVec : Fin 2 → ℝ)
      = (![1, 2] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_two]
  rw [hflow] at h
  have e0 := congrFun h 0
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.head_cons,
    mul_one, Matrix.cons_val_one, one_mul, onesVec] at e0
  exact hf_exp_neg_one_ne_one (by linarith)

/-- **Fence (`hd` of `degreeSqrt_mul_walkLaplacian`)**: entry `(1, 0)`
reads `-√2 ≠ 0` — the commutation genuinely needs positive degrees. -/
theorem hf_comm_hd_fence :
    ¬ (degreeSqrt hfZeroAdj * walkLaplacian hfZeroAdj
      = normalizedLaplacian hfZeroAdj * degreeSqrt hfZeroAdj) := by
  intro h
  have e := congrFun (congrFun h 1) 0
  have hL : (degreeSqrt hfZeroAdj * walkLaplacian hfZeroAdj) 1 0
      = -(Real.sqrt 2) := by
    rw [hfZeroAdj_walkLaplacian]
    simp only [Matrix.mul_apply, degreeSqrt, Matrix.diagonal_apply, hfZeroAdj_deg_one,
      Fin.sum_univ_two, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      if_true, if_false]
    norm_num
  have hR : (normalizedLaplacian hfZeroAdj * degreeSqrt hfZeroAdj) 1 0 = 0 := by
    rw [hfZeroAdj_normalizedLaplacian]
    simp only [Matrix.mul_apply, Matrix.one_apply, degreeSqrt, Matrix.diagonal_apply,
      hfZeroAdj_deg_zero, hfZeroAdj_deg_one, Fin.sum_univ_two, if_true, if_false]
    norm_num
  rw [hL, hR] at e
  exact hf_sqrt_two_ne_zero (by linarith)

/-- **Fence (`hd` of `degreeSqrt_mul_pow_neg_smul_walkLaplacian`)**: the
per-power conjugation at `n = 1`, `t = 1` — same entry, `√2 ≠ 0`. -/
theorem hf_pow_comm_hd_fence :
    ¬ (degreeSqrt hfZeroAdj * (-(1 : ℝ) • walkLaplacian hfZeroAdj) ^ 1
      = (-(1 : ℝ) • normalizedLaplacian hfZeroAdj) ^ 1 * degreeSqrt hfZeroAdj) := by
  rw [pow_one, pow_one]
  intro h
  have e := congrFun (congrFun h 1) 0
  have hL : (degreeSqrt hfZeroAdj * (-(1 : ℝ) • walkLaplacian hfZeroAdj)) 1 0
      = Real.sqrt 2 := by
    rw [hfZeroAdj_walkLaplacian]
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, degreeSqrt,
      Matrix.diagonal_apply, hfZeroAdj_deg_one, Fin.sum_univ_two, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_zero, if_true, if_false, Matrix.neg_apply]
    norm_num
  have hR : ((-(1 : ℝ) • normalizedLaplacian hfZeroAdj) * degreeSqrt hfZeroAdj) 1 0
      = 0 := by
    rw [hfZeroAdj_normalizedLaplacian]
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      degreeSqrt, Matrix.diagonal_apply, hfZeroAdj_deg_zero, hfZeroAdj_deg_one,
      Fin.sum_univ_two, if_true, if_false]
    norm_num
  rw [hL, hR] at e
  exact hf_sqrt_two_ne_zero e

/-- **Fence (`hd` of `degreeSqrt_mulVec_walkHeatKernel`)**: at `t = 1`,
`f = ![1, 0]`, the left side is `(0, √2 e⁻¹) ≠ 0` — the semigroup
conjugation genuinely needs positive degrees. -/
theorem hf_conj_hd_fence :
    ¬ (degreeSqrt hfZeroAdj *ᵥ (walkHeatKernel hfZeroAdj 1 *ᵥ (![1, 0] : Fin 2 → ℝ))
      = normalizedHeatKernel hfZeroAdj 1 *ᵥ (degreeSqrt hfZeroAdj *ᵥ (![1, 0] : Fin 2 → ℝ))) := by
  have hker : normalizedHeatKernel hfZeroAdj 1 = Real.exp (-1 : ℝ) • 1 := by
    rw [normalizedHeatKernel, hfZeroAdj_normalizedLaplacian, one_smul]
    exact hf_exp_neg_one_matrix
  rw [hfZeroAdj_walkHeatKernel_one, hker, Matrix.smul_mulVec_assoc, Matrix.mulVec_smul,
    Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  have hflow : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (![1, 1] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  rw [hflow]
  have hconj : degreeSqrt hfZeroAdj *ᵥ (![1, 1] : Fin 2 → ℝ)
      = (![0, Real.sqrt 2] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, degreeSqrt, Matrix.diagonal_apply,
        hfZeroAdj_deg_zero, hfZeroAdj_deg_one, Fin.sum_univ_two, Real.sqrt_zero]
  rw [hconj]
  have hker2 : degreeSqrt hfZeroAdj *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (![0, 0] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, degreeSqrt, Matrix.diagonal_apply,
        hfZeroAdj_deg_zero, hfZeroAdj_deg_one, Fin.sum_univ_two, Real.sqrt_zero]
  rw [hker2]
  intro h
  have e1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_zero, mul_zero] at e1
  rcases mul_eq_zero.1 e1 with hm | hs
  · exact (Real.exp_ne_zero (-1 : ℝ)) hm
  · exact hf_sqrt_two_ne_zero hs

/-! ### ι — the signed 2-regular fixture `hfRegAdj` -/

def hfRegAdj : Matrix (Fin 2) (Fin 2) ℝ := !![3, -1; -1, 3]

theorem hfRegAdj_isSymm : hfRegAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [hfRegAdj]

theorem hfRegAdj_not_nonneg : ¬ ∀ i j, 0 ≤ hfRegAdj i j := by
  intro h
  have h01 := h 0 1
  simp only [hfRegAdj, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h01
  norm_num at h01

theorem hfRegAdj_deg (i : Fin 2) : deg hfRegAdj i = 2 := by
  fin_cases i <;> simp [deg, hfRegAdj, Fin.sum_univ_two] <;> norm_num

theorem hfRegAdj_hd : ∀ i, 0 < deg hfRegAdj i := by
  intro i
  rw [hfRegAdj_deg]
  norm_num

theorem hfRegAdj_card : 2 ≤ Fintype.card (Fin 2) := le_refl 2

theorem hfRegAdj_degreeInvSqrt :
    degreeInvSqrt hfRegAdj = (√2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  simp only [degreeInvSqrt, Matrix.diagonal_apply, hfRegAdj_deg, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

theorem hfRegAdj_congruence :
    degreeInvSqrt hfRegAdj * hfRegAdj * degreeInvSqrt hfRegAdj
      = (1 / 2 : ℝ) • hfRegAdj := by
  have h1 : ((√2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * hfRegAdj
      = (√2)⁻¹ • hfRegAdj := by
    simp only [Matrix.smul_mul, one_mul]
  have h2 : ((√2)⁻¹ • hfRegAdj) * ((√2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      = ((√2)⁻¹ * (√2)⁻¹) • hfRegAdj := by
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [hfRegAdj_degreeInvSqrt, h1, h2]
  have hcoef : ((√2)⁻¹ * (√2)⁻¹ : ℝ) = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hcoef]

theorem hfRegAdj_normalizedLaplacian :
    normalizedLaplacian hfRegAdj = !![-1 / 2, 1 / 2; 1 / 2, -1 / 2] := by
  rw [normalizedLaplacian, hfRegAdj_congruence]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hfRegAdj] <;> norm_num

theorem hfRegAdj_norm_trace : (normalizedLaplacian hfRegAdj).trace = -1 := by
  simp [Matrix.trace, hfRegAdj_normalizedLaplacian, Fin.sum_univ_two]

theorem hfRegAdj_norm_det : (normalizedLaplacian hfRegAdj).det = 0 := by
  rw [hfRegAdj_normalizedLaplacian, Matrix.det_fin_two]; norm_num

/-- Two-point spectrum pinning, signed variant: a sorted length-two
list with sum `-1` and product `0` is `[-1, 0]`. -/
private theorem hf_two_point_pin_reg {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = -1)
    (hprod : l.prod = 0) :
    l.get ⟨0, by omega⟩ = -1 ∧ l.get ⟨1, by omega⟩ = 0 := by
  obtain ⟨g₀, g₁, hg⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, hf_list_two_eq h2⟩
  subst hg
  have hmono : g₀ ≤ g₁ := hs.rel_get_of_lt (show (0 : Fin 2) < 1 by decide)
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with h0 | h1
  · exfalso
    subst h0
    linarith
  · subst h1
    refine ⟨?_, ?_⟩
    · have h0 : g₀ = -1 := by linarith
      simpa using h0
    · simp

theorem hfRegAdj_evals :
    evals (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) ⟨0, by simp⟩ = -1 ∧
      evals (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) ⟨1, by simp⟩ = 0 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (normalizedLaplacian_symmetric hfRegAdj
          hfRegAdj_isSymm)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (normalizedLaplacian_symmetric hfRegAdj
          hfRegAdj_isSymm)).eigenvalues))).Sorted (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (normalizedLaplacian_symmetric hfRegAdj
          hfRegAdj_isSymm)).eigenvalues))).sum = -1 := by
    have htr : ∑ i : Fin 2, eigvalOf (normalizedLaplacian hfRegAdj)
        (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) i = -1 := by
      rw [eigvalOf_sum_eq_trace, hfRegAdj_norm_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (normalizedLaplacian_symmetric hfRegAdj
          hfRegAdj_isSymm)).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2, ((isHermitian_of_isSymm
        (normalizedLaplacian_symmetric hfRegAdj
          hfRegAdj_isSymm)).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm
        (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm)).det_eq_prod_eigenvalues
      rw [hfRegAdj_norm_det] at hd0
      exact hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact hf_two_point_pin_reg hlen hsorted hsum hprod

theorem hfRegAdj_norm_secondEval_eq_zero :
    secondEval (normalizedLaplacian hfRegAdj)
      (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) hfRegAdj_card = 0 :=
  hfRegAdj_evals.2

theorem hfRegAdj_walkTransition :
    walkTransitionMatrix hfRegAdj = (1 / 2 : ℝ) • hfRegAdj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [walkTransitionMatrix_apply, hfRegAdj_deg] <;>
    simp [Matrix.smul_apply, smul_eq_mul, hfRegAdj]

theorem hfRegAdj_walkLaplacian : walkLaplacian hfRegAdj = normalizedLaplacian hfRegAdj := by
  rw [walkLaplacian, normalizedLaplacian, hfRegAdj_walkTransition, hfRegAdj_congruence]

theorem hfRegAdj_walkLaplacian_mulVec_mode :
    walkLaplacian hfRegAdj *ᵥ (![1, -1] : Fin 2 → ℝ)
      = (-1 : ℝ) • (![1, -1] : Fin 2 → ℝ) := by
  rw [hfRegAdj_walkLaplacian, hfRegAdj_normalizedLaplacian]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, smul_eq_mul] <;>
    norm_num

theorem hfRegAdj_walkHeatKernel_one_mode :
    walkHeatKernel hfRegAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp 1 • (![1, -1] : Fin 2 → ℝ) := by
  rw [walkHeatKernel]
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, one_smul,
    hfRegAdj_walkLaplacian_mulVec_mode, ← neg_smul, neg_neg]

/-- **Fence (`hnn` of `secondEval_le_eigvalOf_normalizedLaplacian_of_ne_zero`)**:
at the index carrying the eigenvalue `-2`, the claim reads
`λ₂(L_sym) = 1 ≤ -2`. The normalized twin, with `hd` genuine (degrees
`2 > 0`). -/
theorem hf_norm_secondEval_nn_fence :
    ∃ i : Fin 2, eigvalOf (normalizedLaplacian hfRegAdj)
        (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) i ≠ 0 ∧
      ¬ (secondEval (normalizedLaplacian hfRegAdj)
          (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) hfRegAdj_card
        ≤ eigvalOf (normalizedLaplacian hfRegAdj)
            (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) i) := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) ⟨0, by simp⟩
  rw [hfRegAdj_evals.1] at hi
  refine ⟨i, ?_, ?_⟩
  · rw [← hi]; norm_num
  · rw [hfRegAdj_norm_secondEval_eq_zero, ← hi]; norm_num

/-- **Fence (`hnn` of `walkHeatKernel_variance_decay`)**: at the signed
regular fixture, `t = 1`, the Fiedler input's π-variance grows by
`e²` — output `4e²` against the rate-`e⁰ = 1` bound on input `4`.
With `hd`, `hA`, `hcard`, `ht` all genuine. -/
theorem hf_walk_var_nn_fence :
    ¬ (∑ i : Fin 2, deg hfRegAdj i * ((walkHeatKernel hfRegAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)) i
        - (∑ j, deg hfRegAdj j * (![1, -1] : Fin 2 → ℝ) j) / (∑ j, deg hfRegAdj j)) ^ 2
      ≤ Real.exp (-(2 * (1 : ℝ) * secondEval (normalizedLaplacian hfRegAdj)
          (normalizedLaplacian_symmetric hfRegAdj hfRegAdj_isSymm) hfRegAdj_card))
        * ∑ i : Fin 2, deg hfRegAdj i * ((![1, -1] : Fin 2 → ℝ) i
          - (∑ j, deg hfRegAdj j * (![1, -1] : Fin 2 → ℝ) j) / (∑ j, deg hfRegAdj j)) ^ 2) := by
  have hdegsum : (∑ j : Fin 2, deg hfRegAdj j) = 4 := by
    rw [Fin.sum_univ_two, hfRegAdj_deg 0, hfRegAdj_deg 1]; norm_num
  have hcross : (∑ j : Fin 2, deg hfRegAdj j * (![1, -1] : Fin 2 → ℝ) j) = 0 := by
    have e0 : deg hfRegAdj 0 * (![1, -1] : Fin 2 → ℝ) 0 = 2 := by
      simp only [Matrix.cons_val_zero, Matrix.head_cons]; rw [hfRegAdj_deg 0]; norm_num
    have e1 : deg hfRegAdj 1 * (![1, -1] : Fin 2 → ℝ) 1 = -2 := by
      simp only [Matrix.cons_val_one, Matrix.head_cons]; rw [hfRegAdj_deg 1]; norm_num
    rw [Fin.sum_univ_two, e0, e1]; norm_num
  rw [hcross, zero_div, hfRegAdj_walkHeatKernel_one_mode,
    hfRegAdj_norm_secondEval_eq_zero]
  simp only [sub_zero]
  have hvarin : ∑ i : Fin 2, deg hfRegAdj i * ((![1, -1] : Fin 2 → ℝ) i) ^ 2 = 4 := by
    have e0 : deg hfRegAdj 0 * ((![1, -1] : Fin 2 → ℝ) 0) ^ 2 = 2 := by
      simp only [Matrix.cons_val_zero, Matrix.head_cons]; rw [hfRegAdj_deg 0]; norm_num
    have e1 : deg hfRegAdj 1 * ((![1, -1] : Fin 2 → ℝ) 1) ^ 2 = 2 := by
      simp only [Matrix.cons_val_one, Matrix.head_cons]; rw [hfRegAdj_deg 1]; norm_num
    rw [Fin.sum_univ_two, e0, e1]; norm_num
  have hvarout : ∑ i : Fin 2, deg hfRegAdj i
        * (((Real.exp 1 • (![1, -1] : Fin 2 → ℝ)) : Fin 2 → ℝ) i) ^ 2
      = 4 * (Real.exp 1) ^ 2 := by
    have e0 : deg hfRegAdj 0 * (((Real.exp 1 • (![1, -1] : Fin 2 → ℝ)) : Fin 2 → ℝ) 0) ^ 2
        = 2 * (Real.exp 1) ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one,
        hfRegAdj_deg 0]
    have e1 : deg hfRegAdj 1 * (((Real.exp 1 • (![1, -1] : Fin 2 → ℝ)) : Fin 2 → ℝ) 1) ^ 2
        = 2 * (Real.exp 1) ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons,
        hfRegAdj_deg 1]
      ring
    rw [Fin.sum_univ_two, e0, e1]
    ring
  rw [hvarout, hvarin, show 2 * (1 : ℝ) * 0 = 0 by norm_num, neg_zero,
    Real.exp_zero, one_mul]
  intro hle
  have hgt : (1 : ℝ) < (Real.exp 1) ^ 2 := by
    nlinarith [hf_exp_one_ge, Real.exp_nonneg 1]
  linarith

end HeatFences

section HeatFencesD1

/-!
### D1 — the walk-twin variance `ht` fence at `K₂ ⊕ K₂` (Fin 4)

  The heat audit's only recorded deferral, closed 2026-09-05
  (`proposals/adversarial-fences-heat-family.md` D1;
  `proposals/qa-name-collision-guard.md` names this as the standing
  frontier's smallest priced completion): `walkHeatKernel_variance_
  decay`'s `ht : 0 ≤ t` clause. The combinatorial twin's `ht` fence
  (fence 19, `hf_var_t_fence` at the Fin 3 `disAdj`) closed the
  mechanism class, but the walk twin's own statement needed a new
  fixture — its kept clauses include `hnn` (nonnegative weights, which
  the signed `hfRegAdj` of the `hnn` fence breaks) and `hd` (positive
  degrees, which `disAdj`'s isolated vertex breaks), so the honest
  `ht`-only failure lives at a genuinely nonnegative, positive-degree,
  disconnected graph: two disjoint edges on `Fin 4`.

  The heaviest single pin the family needed — the four-point
  `secondEval (normalizedLaplacian) = 0` — rides the priced route:
  the upper bound through `secondEval_le_rayleigh` at the centered
  component indicator `![1,1,-1,-1]` (a genuine `L_sym`-kernel
  vector, so its Rayleigh quotient is `0`), the lower bound through
  `normalizedLaplacian_evals_zero` plus `evals_sorted`. The flow pin
  rides `exp_mulVec_eq_smul_of_mulVec_eq_smul` at the per-block
  antisymmetric mode, a genuine `L_walk`-eigenvalue-`2` vector.

  All proofs are real Lean proofs (no `sorry`/`admit`); `#print
  axioms` on every declaration in this section reads exactly
  `propext, Classical.choice, Quot.sound` (theorem instantiations of
  an all-proved shelf; no `-- @refutes` tags — nothing admitted
  consumed). QA proves consequences relative to the substrate, not
  the substrate.
-/

/-- The D1 fixture: two disjoint edges, every degree positive (`1`),
genuinely nonnegative and symmetric — the honest `ht`-only failure
(disconnection holds `λ₂(L_sym)` at `0` while backward time grows the
per-block antisymmetric mode). -/
def hfDis4Adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
      then (1 : ℝ) else 0

theorem hfDis4Adj_isSymm : hfDis4Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [hfDis4Adj]

theorem hfDis4Adj_nonneg : ∀ i j, 0 ≤ hfDis4Adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hfDis4Adj]

theorem hfDis4Adj_deg (i : Fin 4) : deg hfDis4Adj i = 1 := by
  fin_cases i <;> simp [deg, hfDis4Adj, Fin.sum_univ_four]

theorem hfDis4Adj_deg_pos : ∀ i, 0 < deg hfDis4Adj i := by
  intro i
  rw [hfDis4Adj_deg]
  norm_num

theorem hfDis4Adj_card : 2 ≤ Fintype.card (Fin 4) := by decide

theorem hfDis4Adj_degreeInvSqrt : degreeInvSqrt hfDis4Adj = 1 := by
  ext i j
  simp only [degreeInvSqrt, Matrix.diagonal_apply, Matrix.one_apply,
    hfDis4Adj_deg, Real.sqrt_one, inv_one]

theorem hfDis4Adj_normLaplacian :
    normalizedLaplacian hfDis4Adj = 1 - hfDis4Adj := by
  rw [normalizedLaplacian, hfDis4Adj_degreeInvSqrt, one_mul, mul_one]

theorem hfDis4Adj_walkTransition :
    walkTransitionMatrix hfDis4Adj = hfDis4Adj := by
  ext i j
  rw [walkTransitionMatrix_apply, hfDis4Adj_deg, inv_one, one_mul]

theorem hfDis4Adj_walkLaplacian :
    walkLaplacian hfDis4Adj = 1 - hfDis4Adj := by
  rw [walkLaplacian, hfDis4Adj_walkTransition]

theorem hfDis4Adj_mulVec_ones :
    hfDis4Adj *ᵥ (onesVec : Fin 4 → ℝ) = onesVec := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_four,
      hfDis4Adj]

theorem hfDis4Adj_lsym_mulVec_ones :
    normalizedLaplacian hfDis4Adj *ᵥ (onesVec : Fin 4 → ℝ) = 0 := by
  rw [hfDis4Adj_normLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    hfDis4Adj_mulVec_ones, sub_self]

/-- The centered component indicator: block-constant, nonzero,
orthogonal to `onesVec`, and a genuine `L_sym`-kernel vector. -/
def hfDis4KerVec : Fin 4 → ℝ :=
  ![1, 1, -1, -1]

theorem hfDis4KerVec_mulVec :
    hfDis4Adj *ᵥ hfDis4KerVec = hfDis4KerVec := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four, hfDis4Adj,
      hfDis4KerVec]

theorem hfDis4KerVec_ne_zero : hfDis4KerVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [hfDis4KerVec] at h0

theorem hfDis4KerVec_orth_ones :
    Matrix.dotProduct hfDis4KerVec (onesVec : Fin 4 → ℝ) = 0 := by
  simp [Matrix.dotProduct, onesVec, hfDis4KerVec, Fin.sum_univ_four]

theorem hfDis4Adj_lsym_mulVec_ker :
    normalizedLaplacian hfDis4Adj *ᵥ hfDis4KerVec = 0 := by
  rw [hfDis4Adj_normLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    hfDis4KerVec_mulVec, sub_self]

/-- **The four-point `λ₂(L_sym) = 0` pin** — D1's heaviest single
item, at the priced route: the upper bound through
`secondEval_le_rayleigh` at the centered component indicator (a kernel
vector, so its Rayleigh quotient is `0`), the lower bound through
`normalizedLaplacian_evals_zero` plus sortedness of the eigenvalue
list. -/
theorem hfDis4Adj_norm_secondEval_eq_zero :
    secondEval (normalizedLaplacian hfDis4Adj)
      (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
      hfDis4Adj_card = 0 := by
  have hR := secondEval_le_rayleigh
    (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
    (normalizedLaplacian_psd hfDis4Adj hfDis4Adj_isSymm hfDis4Adj_nonneg
      hfDis4Adj_deg_pos)
    hfDis4Adj_lsym_mulVec_ones hfDis4Adj_card hfDis4KerVec_ne_zero
    hfDis4KerVec_orth_ones
  rw [rayleigh, if_neg hfDis4KerVec_ne_zero, quadForm,
    hfDis4Adj_lsym_mulVec_ker, Matrix.dotProduct_zero, zero_div] at hR
  have hge : (0 : ℝ) ≤ secondEval (normalizedLaplacian hfDis4Adj)
      (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
      hfDis4Adj_card := by
    have h0 : evals (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
        ⟨0, by simp⟩ = 0 :=
      normalizedLaplacian_evals_zero hfDis4Adj hfDis4Adj_isSymm
        hfDis4Adj_nonneg hfDis4Adj_deg_pos (by simp)
    have hmono : evals (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
        ⟨0, by simp⟩
      ≤ evals (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
          ⟨1, by simp⟩ :=
      evals_sorted _ (Fin.le_def.2 zero_le_one)
    rw [show secondEval (normalizedLaplacian hfDis4Adj)
          (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
          hfDis4Adj_card
        = evals (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
            ⟨1, by simp⟩ from rfl]
    exact h0 ▸ hmono
  linarith

/-- The per-block antisymmetric mode is a genuine `L_walk`-eigenvalue-`2`
vector: the swap within the first block negates it. -/
theorem hfDis4Adj_walkLaplacian_mulVec_mode :
    walkLaplacian hfDis4Adj *ᵥ (![1, -1, 0, 0] : Fin 4 → ℝ)
      = (2 : ℝ) • (![1, -1, 0, 0] : Fin 4 → ℝ) := by
  have hA : hfDis4Adj *ᵥ (![1, -1, 0, 0] : Fin 4 → ℝ)
      = -(![1, -1, 0, 0] : Fin 4 → ℝ) := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four, hfDis4Adj]
  rw [hfDis4Adj_walkLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec, hA,
    sub_neg_eq_add]
  simp [two_smul]

theorem hfDis4Adj_walkHeatKernel_minus_one_mode :
    walkHeatKernel hfDis4Adj (-1) *ᵥ (![1, -1, 0, 0] : Fin 4 → ℝ)
      = Real.exp 2 • (![1, -1, 0, 0] : Fin 4 → ℝ) := by
  rw [walkHeatKernel]
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  rw [neg_smul, neg_neg, one_smul, hfDis4Adj_walkLaplacian_mulVec_mode]

/-- **Fence (`ht` of `walkHeatKernel_variance_decay`) — D1, the walk
twin.** Backward time at `t = -1` grows the per-block eigenvalue-`2`
mode: output π-variance `2e⁴` against the rate-`e⁰ = 1` bound on
input `2` — disconnection holds the rate at `1` while the flow runs
backward. Every kept clause is genuine at the fixture (the packaged
isolation below). -/
theorem hf_walk_var_t_fence :
    ¬ (∑ i : Fin 4, deg hfDis4Adj i
        * ((walkHeatKernel hfDis4Adj (-1) *ᵥ (![1, -1, 0, 0] : Fin 4 → ℝ)) i
          - (∑ j, deg hfDis4Adj j * (![1, -1, 0, 0] : Fin 4 → ℝ) j)
            / (∑ j, deg hfDis4Adj j)) ^ 2
      ≤ Real.exp (-(2 * (-1 : ℝ) * secondEval (normalizedLaplacian hfDis4Adj)
          (normalizedLaplacian_symmetric hfDis4Adj hfDis4Adj_isSymm)
          hfDis4Adj_card))
        * ∑ i : Fin 4, deg hfDis4Adj i
            * ((![1, -1, 0, 0] : Fin 4 → ℝ) i
              - (∑ j, deg hfDis4Adj j * (![1, -1, 0, 0] : Fin 4 → ℝ) j)
                / (∑ j, deg hfDis4Adj j)) ^ 2) := by
  have hdegsum : (∑ j : Fin 4, deg hfDis4Adj j) = 4 := by
    rw [Finset.sum_congr rfl (fun j _ => hfDis4Adj_deg j)]
    norm_num
  have hcross : (∑ j : Fin 4, deg hfDis4Adj j * (![1, -1, 0, 0] : Fin 4 → ℝ) j)
      = 0 := by
    have e0 : deg hfDis4Adj 0 * (![1, -1, 0, 0] : Fin 4 → ℝ) 0 = 1 := by
      rw [hfDis4Adj_deg]; norm_num
    have e1 : deg hfDis4Adj 1 * (![1, -1, 0, 0] : Fin 4 → ℝ) 1 = -1 := by
      rw [hfDis4Adj_deg]; norm_num
    have e2 : deg hfDis4Adj 2 * (![1, -1, 0, 0] : Fin 4 → ℝ) 2 = 0 := by
      rw [hfDis4Adj_deg]; norm_num
    have e3 : deg hfDis4Adj 3 * (![1, -1, 0, 0] : Fin 4 → ℝ) 3 = 0 := by
      rw [hfDis4Adj_deg]; norm_num
    rw [Fin.sum_univ_four, e0, e1, e2, e3]
    norm_num
  rw [hcross, zero_div, hfDis4Adj_walkHeatKernel_minus_one_mode,
    hfDis4Adj_norm_secondEval_eq_zero]
  simp only [sub_zero]
  have hvarin : ∑ i : Fin 4, deg hfDis4Adj i
      * ((![1, -1, 0, 0] : Fin 4 → ℝ) i) ^ 2 = 2 := by
    have e0 : deg hfDis4Adj 0 * ((![1, -1, 0, 0] : Fin 4 → ℝ) 0) ^ 2 = 1 := by
      rw [hfDis4Adj_deg]; norm_num
    have e1 : deg hfDis4Adj 1 * ((![1, -1, 0, 0] : Fin 4 → ℝ) 1) ^ 2 = 1 := by
      rw [hfDis4Adj_deg]; norm_num
    have e2 : deg hfDis4Adj 2 * ((![1, -1, 0, 0] : Fin 4 → ℝ) 2) ^ 2 = 0 := by
      rw [hfDis4Adj_deg]; norm_num
    have e3 : deg hfDis4Adj 3 * ((![1, -1, 0, 0] : Fin 4 → ℝ) 3) ^ 2 = 0 := by
      rw [hfDis4Adj_deg]; norm_num
    rw [Fin.sum_univ_four, e0, e1, e2, e3]
    norm_num
  have hvarout : ∑ i : Fin 4, deg hfDis4Adj i
      * (((Real.exp 2 • (![1, -1, 0, 0] : Fin 4 → ℝ)) : Fin 4 → ℝ) i) ^ 2
      = 2 * (Real.exp 2) ^ 2 := by
    have e0 : deg hfDis4Adj 0
        * (((Real.exp 2 • (![1, -1, 0, 0] : Fin 4 → ℝ)) : Fin 4 → ℝ) 0) ^ 2
        = (Real.exp 2) ^ 2 := by
      rw [hfDis4Adj_deg]
      simp [Pi.smul_apply, smul_eq_mul]
    have e1 : deg hfDis4Adj 1
        * (((Real.exp 2 • (![1, -1, 0, 0] : Fin 4 → ℝ)) : Fin 4 → ℝ) 1) ^ 2
        = (Real.exp 2) ^ 2 := by
      rw [hfDis4Adj_deg]
      simp [Pi.smul_apply, smul_eq_mul]
    have e2 : deg hfDis4Adj 2
        * (((Real.exp 2 • (![1, -1, 0, 0] : Fin 4 → ℝ)) : Fin 4 → ℝ) 2) ^ 2
        = 0 := by
      rw [hfDis4Adj_deg]
      simp [Pi.smul_apply, smul_eq_mul]
    have e3 : deg hfDis4Adj 3
        * (((Real.exp 2 • (![1, -1, 0, 0] : Fin 4 → ℝ)) : Fin 4 → ℝ) 3) ^ 2
        = 0 := by
      rw [hfDis4Adj_deg]
      simp [Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_four, e0, e1, e2, e3]
    ring
  rw [hvarout, hvarin, show 2 * (-1 : ℝ) * 0 = 0 by norm_num, neg_zero,
    Real.exp_zero, one_mul]
  intro hle
  have hgt : (1 : ℝ) < (Real.exp 2) ^ 2 := by
    nlinarith [hf_exp_two_gt_one, Real.exp_nonneg 2]
  linarith

/-- Packaged isolation for the D1 fence: every kept clause of
`walkHeatKernel_variance_decay` is genuine at the fixture, and the
dropped `ht : 0 ≤ t` genuinely fails at `t = -1`. -/
theorem hfDis4Adj_isolation :
    hfDis4Adj.IsSymm
      ∧ (∀ i j, 0 ≤ hfDis4Adj i j)
      ∧ (∀ i, 0 < deg hfDis4Adj i)
      ∧ 2 ≤ Fintype.card (Fin 4)
      ∧ (-1 : ℝ) < 0 :=
  ⟨hfDis4Adj_isSymm, hfDis4Adj_nonneg, hfDis4Adj_deg_pos, hfDis4Adj_card,
    by norm_num⟩


/-! ### The QA pieces (destined for Heat_QA.lean) -/

/-- **The scalar engine pinned at `y = 2`** through the theorem: the
displacement factor of the eigenvalue-`2` mode at `t = 1`. -/
theorem gsc_scalar_two_QA :
    (1 - Real.exp (-(2:ℝ))) ^ 2 ≤ (2:ℝ) ^ 2 :=
  sq_one_sub_exp_neg_le (by norm_num : (0:ℝ) ≤ 2)

/-- **The global bound instantiated where the windowed bound's
hypothesis fails** — the delivery's payoff pin. At `t = 1` on K₂ the
mode displacement is `(1 − e^{−2}) • ![1,−1]`, while `t·λ = 2`
violates the windowed bound's `|t·λᵢ| ≤ 1` (the fence
`heatKernel_edge_remainder_window_fenced_QA`); the global bound
applies THROUGH the theorem at exactly the point the windowed one
cannot. -/
theorem gsc_K2_t1_QA :
    Matrix.dotProduct
        ((![1, -1] : Fin 2 → ℝ) - heatKernel heatEdgeAdj 1 *ᵥ (![1, -1]))
        ((![1, -1] : Fin 2 → ℝ) - heatKernel heatEdgeAdj 1 *ᵥ (![1, -1]))
      ≤ 1 ^ 2 * Matrix.dotProduct (laplacian heatEdgeAdj *ᵥ (![1, -1]))
          (laplacian heatEdgeAdj *ᵥ (![1, -1])) :=
  heatKernel_globalContraction_dotProduct_le heatEdgeAdj
    heatEdgeAdj_isSymm heatEdgeAdj_nonneg zero_le_one (![1, -1])

/-- **Both sides of the payoff pin evaluated**: the RHS is exactly `8`
(the mode is a `2`-eigenvector: `(2•m) ⬝ᵥ (2•m) = 4·2`), the LHS at
most `2` (the displacement factor lies in `[0, 1]`, the mode's
self-pairing is `2`) — the instantiation is non-vacuous, with genuine
slack, at the windowed bound's failure point. -/
theorem gsc_K2_t1_values_QA :
    Matrix.dotProduct
        ((![1, -1] : Fin 2 → ℝ) - heatKernel heatEdgeAdj 1 *ᵥ (![1, -1]))
        ((![1, -1] : Fin 2 → ℝ) - heatKernel heatEdgeAdj 1 *ᵥ (![1, -1]))
      ≤ 2
      ∧ 8 = 1 ^ 2 * Matrix.dotProduct
          (laplacian heatEdgeAdj *ᵥ (![1, -1]))
          (laplacian heatEdgeAdj *ᵥ (![1, -1])) := by
  have he : Real.exp (-(2:ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (neg_nonpos.2 (by norm_num : (0:ℝ) ≤ 2))
  have he0 := Real.exp_nonneg (-(2:ℝ))
  have hval := sq_le_sq'
    (by linarith : -(1:ℝ) ≤ 1 - Real.exp (-(2:ℝ)))
    (by linarith : 1 - Real.exp (-(2:ℝ)) ≤ 1)
  have hK' : heatKernel heatEdgeAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp (-(2 * 1 : ℝ)) • (![1, -1] : Fin 2 → ℝ) :=
    heatKernel_edge_mode_raw_QA 1 one_ne_zero
  have hK : heatKernel heatEdgeAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp (-(2:ℝ)) • (![1, -1] : Fin 2 → ℝ) := by
    rw [show (2:ℝ) * 1 = 2 from by norm_num] at hK'
    exact hK'
  refine ⟨?_, ?_⟩
  · rw [hK]
    have hdd : Matrix.dotProduct
        ((![1, -1] : Fin 2 → ℝ) - Real.exp (-(2:ℝ)) • (![1, -1]))
        ((![1, -1] : Fin 2 → ℝ) - Real.exp (-(2:ℝ)) • (![1, -1]))
        = (1 - Real.exp (-(2:ℝ))) ^ 2 * 2 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    rw [hdd]
    nlinarith [hval]
  · rw [edgeLaplacian_mulVec_mode]
    have hdot : Matrix.dotProduct ((2:ℝ) • (![1, -1] : Fin 2 → ℝ))
        ((2:ℝ) • (![1, -1] : Fin 2 → ℝ)) = 8 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
      norm_num
    rw [hdot]
    norm_num

/-- **The Euclidean form pinned at the same point**: the request's
first formula, verbatim, at `t = 1` on K₂ through the Step-2
corollary. -/
theorem gsc_K2_norm_t1_QA :
    ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm
        ((![1, -1] : Fin 2 → ℝ)
          - heatKernel heatEdgeAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ))‖
      ≤ 1 * ‖(WithLp.equiv 2 (Fin 2 → ℝ)).symm
          (laplacian heatEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))‖ :=
  heatKernel_globalContraction_le heatEdgeAdj heatEdgeAdj_isSymm
    heatEdgeAdj_nonneg zero_le_one (![1, -1])

/-- **The general-probe dissipation bound pinned at K₂, `t = 1`**: the
probe `e₀ = ![1,0]` (the K₂ region indicator `{0}`) read against the
mode input `![1,−1]` — the left side evaluates to `1 − e^{−2}` (the
indicator pairs with the mode's first entry), the right side to
`1 · √(L e₀ ⬝ᵥ L e₀) · √(m ⬝ᵥ m) = √2 · √2 = 2` (the probe's Laplacian
action is the OUTFLOW vector `![1,−1]` — the Boundary Outflow Lemma's
own object). -/
theorem gsc_dissipation_K2_QA :
    |Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
        ((![1, -1] : Fin 2 → ℝ)
          - heatKernel heatEdgeAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ))|
      ≤ 1 * Real.sqrt (Matrix.dotProduct
          (laplacian heatEdgeAdj *ᵥ (![1, 0] : Fin 2 → ℝ))
          (laplacian heatEdgeAdj *ᵥ (![1, 0] : Fin 2 → ℝ)))
        * Real.sqrt (Matrix.dotProduct (![1, -1] : Fin 2 → ℝ)
          (![1, -1] : Fin 2 → ℝ)) := by
  have h := abs_dotProduct_heatFlow_le heatEdgeAdj heatEdgeAdj_isSymm
    heatEdgeAdj_nonneg zero_le_one (![1, 0] : Fin 2 → ℝ)
    (![1, -1] : Fin 2 → ℝ)
  have hL0 : laplacian heatEdgeAdj *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (![1, -1] : Fin 2 → ℝ) := by
    rw [edgeLaplacian_eq]
    funext i
    fin_cases i <;>
      simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.of_apply] <;>
      norm_num
  rw [hL0] at h
  have he : Real.exp (-(2:ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (neg_nonpos.2 (by norm_num : (0:ℝ) ≤ 2))
  have he0 := Real.exp_nonneg (-(2:ℝ))
  have hK' : heatKernel heatEdgeAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp (-(2 * 1 : ℝ)) • (![1, -1] : Fin 2 → ℝ) :=
    heatKernel_edge_mode_raw_QA 1 one_ne_zero
  have hK : heatKernel heatEdgeAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp (-(2:ℝ)) • (![1, -1] : Fin 2 → ℝ) := by
    rw [show (2:ℝ) * 1 = 2 from by norm_num] at hK'
    exact hK'
  -- LHS value: e₀ ⬝ᵥ ((1 − e⁻²) • m) = 1 − e⁻² ≥ 0
  have hval : Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
      ((![1, -1] : Fin 2 → ℝ) - Real.exp (-(2:ℝ)) • (![1, -1]))
      = 1 - Real.exp (-(2:ℝ)) := by
    simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have h2 : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ)
      (![1, -1] : Fin 2 → ℝ) = 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  rw [hK, hval,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.exp (-(2:ℝ))),
    h2, one_mul, ← pow_two (Real.sqrt 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h
  rw [hK, hval,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.exp (-(2:ℝ))),
    hL0, h2, one_mul, ← pow_two (Real.sqrt 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  exact h

/-! ### The `hnonneg` fence (destined for Heat_QA.lean) -/

/-- The signed K₂ fence fixture: arc weight `−1` — symmetric, with the
Laplacian's mode eigenvalue NEGATIVE (`−2`), so `e^{−tL}` genuinely
grows on the mode. `hnonneg` fails (entry `−1`), `hA` holds. -/
def gscSignedAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; -1, 0]

theorem gscSigned_isSymm : gscSignedAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [gscSignedAdj]

/-- The signed Laplacian is `!![−1, 1; 1, −1]]` — degrees `−1`, so the
mode `![1,−1]` is an eigenvector at eigenvalue `−2`. -/
theorem gscSigned_laplacian :
    laplacian gscSignedAdj = !![-1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [laplacian, Matrix.sub_apply, degreeMatrix,
      Matrix.diagonal_apply, deg, gscSignedAdj, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply] <;>
    norm_num

theorem gscSigned_lap_mulVec_mode :
    laplacian gscSignedAdj *ᵥ (![1, -1] : Fin 2 → ℝ)
      = (-(2 : ℝ)) • (![1, -1] : Fin 2 → ℝ) := by
  rw [gscSigned_laplacian]
  funext i
  fin_cases i <;>
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply, Pi.smul_apply, smul_eq_mul] <;>
    norm_num

/-- **The `hnonneg` fence**: on the signed fixture the global order-0
bound's conclusion GENUINELY FAILS at `t = 1` — the mode's displacement
factor is `1 − e^{2}` (growth, `3 < e²` by `Real.add_one_lt_exp`), so
the LHS is `2(e² − 1)² > 2·4 = 8` while the RHS is
`1² · ((−2•m) ⬝ᵥ (−2•m)) = 8`. Every other hypothesis holds
(`hA` genuine at the symmetric signed fixture; `t = 1 ≥ 0`) — the
nonnegativity hypothesis is load-bearing, not decorative. -/
theorem gsc_hnonneg_fence_QA :
    ¬ (∀ i j, 0 ≤ gscSignedAdj i j) ∧
    ¬ (Matrix.dotProduct
        ((![1, -1] : Fin 2 → ℝ)
          - heatKernel gscSignedAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ))
        ((![1, -1] : Fin 2 → ℝ)
          - heatKernel gscSignedAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ))
      ≤ 1 ^ 2 * Matrix.dotProduct
          (laplacian gscSignedAdj *ᵥ (![1, -1] : Fin 2 → ℝ))
          (laplacian gscSignedAdj *ᵥ (![1, -1] : Fin 2 → ℝ))) := by
  have he2 : (3 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp two_ne_zero
    linarith
  -- the heat kernel GROWS on the mode: K₁ m = e² • m
  have hM : (-(((1 : ℝ) • laplacian gscSignedAdj))) *ᵥ (![1, -1] : Fin 2 → ℝ)
      = (2 : ℝ) • (![1, -1] : Fin 2 → ℝ) := by
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc,
      gscSigned_lap_mulVec_mode]
    simp
  have hK : heatKernel gscSignedAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp 2 • (![1, -1] : Fin 2 → ℝ) := by
    rw [heatKernel]
    exact exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ hM
  refine ⟨fun h => by
      have h01 := h 0 1
      simp only [gscSignedAdj, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.of_apply] at h01
      norm_num at h01, ?_⟩
  have hdisp : (![1, -1] : Fin 2 → ℝ)
        - Real.exp 2 • (![1, -1] : Fin 2 → ℝ)
      = (1 - Real.exp 2) • (![1, -1] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;>
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      ring
  have hLHS : Matrix.dotProduct
      ((![1, -1] : Fin 2 → ℝ)
        - heatKernel gscSignedAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ))
      ((![1, -1] : Fin 2 → ℝ)
        - heatKernel gscSignedAdj 1 *ᵥ (![1, -1] : Fin 2 → ℝ))
      = 2 * (Real.exp 2 - 1) ^ 2 := by
    have hdd : Matrix.dotProduct
        ((1 - Real.exp 2) • (![1, -1] : Fin 2 → ℝ))
        ((1 - Real.exp 2) • (![1, -1] : Fin 2 → ℝ))
        = (1 - Real.exp 2) ^ 2 * 2 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [hK, hdisp, hdd]
    ring
  have hRHS : 1 ^ 2 * Matrix.dotProduct
      (laplacian gscSignedAdj *ᵥ (![1, -1] : Fin 2 → ℝ))
      (laplacian gscSignedAdj *ᵥ (![1, -1] : Fin 2 → ℝ)) = 8 := by
    have hdd : Matrix.dotProduct ((-(2 : ℝ)) • (![1, -1] : Fin 2 → ℝ))
        ((-(2 : ℝ)) • (![1, -1] : Fin 2 → ℝ)) = 8 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Pi.smul_apply, smul_eq_mul]
      norm_num
    rw [gscSigned_lap_mulVec_mode, hdd]
    norm_num
  rw [hLHS, hRHS]
  have hpos : (0 : ℝ) < Real.exp 2 - 1 := by linarith
  have hgt : (4 : ℝ) < (Real.exp 2 - 1) ^ 2 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < Real.exp 2 - 3)
      (by linarith : (0:ℝ) < Real.exp 2 + 1),
      mul_pos (by linarith : (0:ℝ) < Real.exp 2 - 3)
        (by linarith : (0:ℝ) < Real.exp 2 - 1)]
  linarith

/-- **The `ht` fence**: on the plain nonnegative `K₂` fixture — `hA`
and `hnonneg` both GENUINE, so every hypothesis except `0 ≤ t` holds —
the global order-0 bound's conclusion GENUINELY FAILS at `t = -1`
(backward time): the mode's displacement factor is `1 − e^{2}` (the
semigroup runs backward, `e^{-tL} m = e^{2} • m` on the eigenvalue-`2`
mode, growth), so the LHS is `2(e² − 1)² > 2·4 = 8` while the RHS is
`(-1)² · (Lm ⬝ᵥ Lm) = (2m ⬝ᵥ 2m) = 8`. The forward-time hypothesis is
load-bearing, not decorative — and it is inherited transitively by
`heatKernel_globalContraction_le`, `abs_dotProduct_heatFlow_le`, and
the Boundary Outflow Part-2 statement itself. -/
theorem gsc_ht_fence_QA :
    heatEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ heatEdgeAdj i j)
      ∧ ¬ (Matrix.dotProduct
          ((![1, -1] : Fin 2 → ℝ)
            - heatKernel heatEdgeAdj (-1) *ᵥ (![1, -1] : Fin 2 → ℝ))
          ((![1, -1] : Fin 2 → ℝ)
            - heatKernel heatEdgeAdj (-1) *ᵥ (![1, -1] : Fin 2 → ℝ))
        ≤ (-1 : ℝ) ^ 2 * Matrix.dotProduct
            (laplacian heatEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))
            (laplacian heatEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))) := by
  have he2 : (3 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp two_ne_zero
    linarith
  refine ⟨heatEdgeAdj_isSymm, heatEdgeAdj_nonneg, ?_⟩
  -- backward time: the exponent matrix IS the Laplacian, and the mode
  -- is its eigenvalue-2 eigenvector, so the kernel GROWS on the mode
  have hM : (-(((-1 : ℝ) • laplacian heatEdgeAdj)) *ᵥ (![1, -1] : Fin 2 → ℝ))
      = (2 : ℝ) • (![1, -1] : Fin 2 → ℝ) := by
    have hn : (-(((-1 : ℝ) • laplacian heatEdgeAdj)))
        = laplacian heatEdgeAdj := by simp
    rw [hn]
    exact edgeLaplacian_mulVec_mode
  have hK : heatKernel heatEdgeAdj (-1) *ᵥ (![1, -1] : Fin 2 → ℝ)
      = Real.exp 2 • (![1, -1] : Fin 2 → ℝ) := by
    rw [heatKernel]
    exact exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ hM
  have hdisp : (![1, -1] : Fin 2 → ℝ)
        - Real.exp 2 • (![1, -1] : Fin 2 → ℝ)
      = (1 - Real.exp 2) • (![1, -1] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;>
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
      ring
  have hLHS : Matrix.dotProduct
      ((![1, -1] : Fin 2 → ℝ)
        - heatKernel heatEdgeAdj (-1) *ᵥ (![1, -1] : Fin 2 → ℝ))
      ((![1, -1] : Fin 2 → ℝ)
        - heatKernel heatEdgeAdj (-1) *ᵥ (![1, -1] : Fin 2 → ℝ))
      = 2 * (Real.exp 2 - 1) ^ 2 := by
    have hdd : Matrix.dotProduct
        ((1 - Real.exp 2) • (![1, -1] : Fin 2 → ℝ))
        ((1 - Real.exp 2) • (![1, -1] : Fin 2 → ℝ))
        = (1 - Real.exp 2) ^ 2 * 2 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [hK, hdisp, hdd]
    ring
  have hRHS : (-1 : ℝ) ^ 2 * Matrix.dotProduct
      (laplacian heatEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))
      (laplacian heatEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)) = 8 := by
    have hdd : Matrix.dotProduct ((2 : ℝ) • (![1, -1] : Fin 2 → ℝ))
        ((2 : ℝ) • (![1, -1] : Fin 2 → ℝ)) = 8 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Pi.smul_apply, smul_eq_mul]
      norm_num
    rw [edgeLaplacian_mulVec_mode, hdd]
    norm_num
  rw [hLHS, hRHS]
  have hgt : (4 : ℝ) < (Real.exp 2 - 1) ^ 2 := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < Real.exp 2 - 3)
      (by linarith : (0 : ℝ) < Real.exp 2 + 1),
      mul_pos (by linarith : (0 : ℝ) < Real.exp 2 - 3)
        (by linarith : (0 : ℝ) < Real.exp 2 - 1)]
  linarith

end HeatFencesD1

/-! ## The heat pair's structural pins
(`proposals/heat-irreducible-pairs-pins.md`)

The consumption census (`wip/census_20260907_post10.txt`, inert set 25)
leaves `heatKernel_decayFactor_le_one` and `normalizedHeatKernel_zero`
never consumed — the decay-factor family's `ht` fences exist on file
(the backward-time refutations below), but the positive `0 ≤ t`
statement was never instantiated. This section pins both: the decay
factor attained with equality at the constant mode (the undamped
kernel — the bound sharp) and strictly below at the Fiedler mode; the
`t = 0` identity acting on a nontrivial vector through the theorem.
-/

section StructuralPins

/-- **The decay-factor bound at the constant mode — attained with
equality**: at the pinned `evals ⟨0⟩ = 0` the factor is `e^{-t·0} = 1`
exactly, so the `≤ 1` bound is the sharp statement that the kernel
mode is undamped, never amplified. -/
theorem hkp_decay_kernel_le_QA :
    Real.exp (-((1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj
          heatEdgeAdj_isSymm) ⟨0, by simp⟩)) ≤ 1 :=
  heatKernel_decayFactor_le_one heatEdgeAdj heatEdgeAdj_isSymm
    heatEdgeAdj_nonneg (by norm_num) ⟨0, by simp⟩

theorem hkp_decay_kernel_value_QA :
    Real.exp (-((1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj
          heatEdgeAdj_isSymm) ⟨0, by simp⟩)) = 1 := by
  rw [(edgeLaplacian_evals_QA).1, mul_zero, neg_zero, Real.exp_zero]

/-- **The decay-factor bound at the Fiedler mode**: at the pinned
`evals ⟨1⟩ = 2`, `t = 1`, the factor is `e^{-2} ≤ 1` — and strictly
below, by the file's established `Real.exp_lt_exp` idiom. -/
theorem hkp_decay_fiedler_le_QA :
    Real.exp (-((1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj
          heatEdgeAdj_isSymm) ⟨1, by simp⟩)) ≤ 1 :=
  heatKernel_decayFactor_le_one heatEdgeAdj heatEdgeAdj_isSymm
    heatEdgeAdj_nonneg (by norm_num) ⟨1, by simp⟩

theorem hkp_decay_fiedler_strict_QA :
    Real.exp (-((1 : ℝ) * evals (laplacian_symmetric heatEdgeAdj
          heatEdgeAdj_isSymm) ⟨1, by simp⟩)) < 1 := by
  rw [(edgeLaplacian_evals_QA).2]
  have h : Real.exp (-((1 : ℝ) * 2)) < Real.exp (0 : ℝ) :=
    Real.exp_lt_exp.2 (by norm_num)
  rw [Real.exp_zero] at h
  exact h

/-- **The `t = 0` identity acting on a nontrivial vector**: the
normalized heat kernel at time zero is exactly `1`, so it fixes the
antisymmetric vector — through the theorem, no matrix exponential
computed. -/
theorem nhk_zero_action_pin_QA :
    normalizedHeatKernel heatEdgeAdj 0 *ᵥ (![1, -1] : Fin 2 → ℝ)
      = ![1, -1] := by
  rw [normalizedHeatKernel_zero, Matrix.one_mulVec]

end StructuralPins

end SpectralGraphTheory.QA
