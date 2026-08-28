/-
  EdgePerturbation.lean

  Purpose
  -------
  The deterministic engine for `matrix_hoeffding`'s first theorem consumer
  (`proposals/matrix-hoeffding-spectral-gap-estimation.md`, Step 1):
  independent, centered, bounded per-event Laplacian perturbations on the
  product-Bernoulli sampling space.

  Three layers, all pure hard crust (no axiom contact):

  1. the single-edge algebra — the adjacency `edgeAdj i j w` of the graph
     that is `w` on the pair `{i, j}` and zero elsewhere, its row sums, and
     the identity `L(edge i j w) = w • (e_i − e_j)(e_i − e_j)ᵀ` joining it
     to the `rankOne` algebra of `GraphTheory.Sparsification`;
  2. the `Matrix.PosSemidef` helpers the pinned Mathlib lacks (scaling and
     squares of symmetric matrices);
  3. the centered Bernoulli edge-perturbation design — `perturbEdgeLap`
     (the single-edge Laplacian block) and `perturbSummand`
     (`(δ_e − p_e) • L_e`) — with every hypothesis clause of the repaired
     `matrix_hoeffding` axiom proved at the design: measurability and
     pairwise independence transfer through `Probability.BernoulliProduct`'s
     matrix layer, Hermitianity is rank-one symmetry, and the semidefinite
     bound `X_e² ⪯ L_e²` reduces to the interval `(δ_e − p_e)² ≤ 1` — no
     hypothesis on the weight matrix `A` at all (the design is sign-free:
     squares of symmetric matrices are positive semidefinite).

  The axiom-backed tail theorems live in `Scaffold/Derived/
  EdgePerturbationTail.lean`; QA in `Scaffold/QA/Derived/
  EdgePerturbation_QA.lean`.
-/

import Scaffold.Mathlib.GraphTheory.Sparsification
import Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding
import Mathlib.LinearAlgebra.Matrix.PosDef

open MeasureTheory ProbabilityTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open scoped BigOperators Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## 1. The single-edge algebra -/

/-- The single-edge adjacency at weight `w`: `w` at `(i, j)` and `(j, i)`,
zero elsewhere (at `i = j` a loop of weight `w`). -/
def edgeAdj (i j : V) (w : ℝ) : Matrix V V ℝ :=
  Matrix.of fun a b => if a = i ∧ b = j then w else if a = j ∧ b = i then w else 0

omit [Fintype V] in
theorem edgeAdj_apply (i j : V) (w : ℝ) (a b : V) :
    edgeAdj i j w a b = if a = i ∧ b = j then w else if a = j ∧ b = i then w else 0 :=
  rfl

omit [Fintype V] in
theorem edgeAdj_isSymm (i j : V) (w : ℝ) : (edgeAdj i j w).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  simp only [Matrix.transpose_apply, edgeAdj_apply]
  by_cases h1 : a = i <;> by_cases h2 : a = j <;> by_cases h3 : b = i <;>
    by_cases h4 : b = j <;> simp [h1, h2, h3, h4]

/-- The row sums of the single-edge adjacency: `w` on `i` and `j`. -/
theorem deg_edgeAdj (i j : V) (w : ℝ) (a : V) :
    deg (edgeAdj i j w) a = if a = i ∨ a = j then w else 0 := by
  by_cases hii : i = j
  · rw [hii]
    by_cases haj : a = j
    · have hrow : ∀ b : V, edgeAdj j j w a b = if b = j then w else 0 := by
        intro b
        rw [edgeAdj_apply]
        by_cases hbj : b = j <;> simp [haj, hbj]
      simp only [deg, hrow]
      simp [haj]
    · have hrow : ∀ b : V, edgeAdj j j w a b = 0 := by
        intro b
        rw [edgeAdj_apply, if_neg (fun h : a = j ∧ b = j => haj h.1),
          if_neg (fun h : a = j ∧ b = j => haj h.1)]
      simp only [deg, hrow]
      simp [haj]
  · by_cases hai : a = i
    · rw [hai]
      have hrow : ∀ b : V, edgeAdj i j w i b = if b = j then w else 0 := by
        intro b
        rw [edgeAdj_apply, if_neg (fun h : i = j ∧ b = i => hii h.1)]
        simp
      simp only [deg, hrow]
      simp [hii]
    · by_cases haj : a = j
      · rw [haj]
        have hrow : ∀ b : V, edgeAdj i j w j b = if b = i then w else 0 := by
          intro b
          rw [edgeAdj_apply, if_neg (fun h : j = i ∧ b = j => hii h.1.symm)]
          simp
        simp only [deg, hrow]
        simp [hii]
      · have hrow : ∀ b : V, edgeAdj i j w a b = 0 := by
          intro b
          rw [edgeAdj_apply, if_neg (fun h : a = i ∧ b = j => hai h.1),
            if_neg (fun h : a = j ∧ b = i => haj h.1)]
        simp only [deg, hrow]
        simp [hai, haj]

/-- **The Laplacian of the single-edge graph is the rank-one edge block**:
`L(edge i j w) = w • (e_i − e_j)(e_i − e_j)ᵀ` — valid also at `i = j`,
where both sides are zero. This joins the edge-perturbation design to the
`rankOne` algebra (norm bound, PSD, quadratic form) of
`GraphTheory.Sparsification`. -/
theorem laplacian_edgeAdj (i j : V) (w : ℝ) :
    laplacian (edgeAdj i j w)
      = w • rankOne (Pi.single i 1 - Pi.single j 1) := by
  ext a b
  simp only [laplacian, degreeMatrix, Matrix.of_apply, dif_eq_if,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, rankOne_apply,
    edgeAdj_apply]
  rw [deg_edgeAdj]
  by_cases hii : i = j <;> by_cases h1 : a = i <;> by_cases h2 : a = j <;>
    by_cases h3 : b = i <;> by_cases h4 : b = j <;> by_cases hab : a = b <;>
    simp_all [Pi.single_apply, eq_comm]

/-! ## 2. Positive-semidefiniteness helpers the pin lacks -/

/-- Nonnegative scaling preserves positive semidefiniteness. The pinned
Mathlib has `PosSemidef.add` and `PosSemidef.pow` but no scaling lemma;
this is the semidefinite-order clause's arithmetic for real matrices. -/
theorem posSemidef_smul_nonneg {M : Matrix V V ℝ} (hM : M.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : (c • M).PosSemidef := by
  have hT : Mᵀ = M := (Matrix.conjTranspose_eq_transpose_of_trivial M).symm.trans hM.1
  have hsm : (c • M)ᵀ = c • M := by
    rw [Matrix.transpose_smul]; exact congrArg (c • ·) hT
  refine ⟨isHermitian_of_isSymm hsm, fun x => ?_⟩
  show 0 ≤ Matrix.dotProduct x ((c • M) *ᵥ x)
  rw [Matrix.smul_mulVec_assoc, Matrix.dotProduct_smul, smul_eq_mul]
  exact mul_nonneg hc (hM.2 x)

/-- Every rank-one symmetric matrix is positive semidefinite: its
quadratic form is a square (`rankOne_quadForm`). -/
theorem rankOne_posSemidef (v : V → ℝ) : (rankOne v).PosSemidef := by
  refine ⟨isHermitian_of_isSymm (rankOne_isSymm v), fun x => ?_⟩
  show 0 ≤ Matrix.dotProduct x (rankOne v *ᵥ x)
  rw [show Matrix.dotProduct x (rankOne v *ᵥ x) = quadForm (rankOne v) x from rfl,
    rankOne_quadForm]
  exact sq_nonneg _

/-- **The square of a symmetric matrix is positive semidefinite** — no
positive-semidefiniteness hypothesis on `M` itself (eigenvalues square).
Through the self-adjoint coordinate form
`dotProduct_mulVec_comm_of_isSymm` — its first consumer outside the
projector-uniqueness layer. -/
theorem posSemidef_mul_self_of_isSymm {M : Matrix V V ℝ} (hM : M.IsSymm) :
    (M * M).PosSemidef := by
  have hmul : (M * M)ᵀ = M * M := by
    rw [Matrix.transpose_mul, hM.eq]
  refine ⟨isHermitian_of_isSymm hmul, fun x => ?_⟩
  show 0 ≤ Matrix.dotProduct x ((M * M) *ᵥ x)
  rw [← Matrix.mulVec_mulVec x M M]
  rw [dotProduct_mulVec_comm_of_isSymm hM x (M *ᵥ x)]
  exact dotProduct_self_nonneg _

/-! ## 3. The centered Bernoulli edge-perturbation design -/

section Design

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- The single-edge Laplacian block of the ordered pair `e`:
`A e.1 e.2 • (e_{e.1} − e_{e.2})(e_{e.1} − e_{e.2})ᵀ` — by
`laplacian_edgeAdj` exactly the Laplacian of the single-edge graph at
`e` with the weight `A` assigns it. -/
def perturbEdgeLap (A : WAdj (V := V)) (e : V × V) : Matrix V V ℝ :=
  A e.1 e.2 • rankOne (Pi.single e.1 1 - Pi.single e.2 1)

omit [Fintype V] in
theorem perturbEdgeLap_isSymm (e : V × V) : (perturbEdgeLap A e).IsSymm := by
  show (perturbEdgeLap A e)ᵀ = perturbEdgeLap A e
  rw [perturbEdgeLap, Matrix.transpose_smul]
  exact congrArg (A e.1 e.2 • ·) (rankOne_isSymm _).eq

/-- `L(edgeAdj e) = perturbEdgeLap A e`: the design's blocks really are
Laplacians of single-edge graphs. -/
theorem laplacian_edgeAdj_eq_perturbEdgeLap (e : V × V) :
    laplacian (edgeAdj e.1 e.2 (A e.1 e.2)) = perturbEdgeLap A e :=
  laplacian_edgeAdj e.1 e.2 (A e.1 e.2)

theorem perturbEdgeLap_posSemidef (e : V × V) (h : 0 ≤ A e.1 e.2) :
    (perturbEdgeLap A e).PosSemidef :=
  posSemidef_smul_nonneg (rankOne_posSemidef _) h

/-- The centered Bernoulli summand of the ordered pair `e` at outcome
`ω`: `(δ_e(ω) − p e) • L_e`, where `δ_e` is the coordinate indicator of
the product-Bernoulli space. Centering makes the design's expected
perturbation zero; no saturation guard is needed (Hoeffding's
semidefinite bound has no division by the sampling probability). -/
def perturbSummand (A : WAdj (V := V)) (p : (V × V) → ℝ) (e : V × V)
    (ω : (V × V) → Bool) : Matrix V V ℝ :=
  ((if ω e then (1 : ℝ) else 0) - p e) • perturbEdgeLap A e

omit [Fintype V] in
theorem perturbSummand_isSymm (e : V × V) (ω : (V × V) → Bool) :
    (perturbSummand A p e ω).IsSymm := by
  show (perturbSummand A p e ω)ᵀ = perturbSummand A p e ω
  rw [perturbSummand, Matrix.transpose_smul]
  exact congrArg (((if ω e then (1 : ℝ) else 0) - p e) • ·)
    (perturbEdgeLap_isSymm A e).eq

/-- The square of the centered summand: `X_e² = (δ_e − p_e)² • L_e²`. -/
theorem perturbSummand_mul_self (e : V × V) (ω : (V × V) → Bool) :
    perturbSummand A p e ω * perturbSummand A p e ω
      = (((if ω e then (1 : ℝ) else 0) - p e) ^ 2) •
        (perturbEdgeLap A e * perturbEdgeLap A e) := by
  rw [perturbSummand, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

/-- **The semidefinite bound of the design**: `X_e(ω)² ⪯ L_e²` for every
outcome, with the bound matrix `A e := L_e` itself. The design is
sign-free — no hypothesis on the weight `A e.1 e.2` (nor on symmetry of
`A`), because `L_e` is symmetric for every weight and squares of symmetric
matrices are positive semidefinite; the only load-bearing hypothesis is
the sampling interval `p e ∈ [0, 1]`, through
`(δ_e(ω) − p e) ^ 2 ≤ 1`. This is the `h_bound` clause of
`matrix_hoeffding` at the design. -/
theorem perturbSummand_sq_le (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (e : V × V) (ω : (V × V) → Bool) :
    (perturbEdgeLap A e * perturbEdgeLap A e
      - perturbSummand A p e ω * perturbSummand A p e ω).PosSemidef := by
  have hdiff : perturbEdgeLap A e * perturbEdgeLap A e
      - perturbSummand A p e ω * perturbSummand A p e ω
      = (1 - ((if ω e then (1 : ℝ) else 0) - p e) ^ 2) •
        (perturbEdgeLap A e * perturbEdgeLap A e) := by
    rw [perturbSummand_mul_self A p e ω, sub_smul, one_smul]
  rw [hdiff]
  refine posSemidef_smul_nonneg
    (posSemidef_mul_self_of_isSymm (perturbEdgeLap_isSymm A e)) ?_
  by_cases hω : ω e
  · have hc : ((1 : ℝ) - p e) ^ 2 ≤ 1 := by
      nlinarith [hp0 e, hp1 e, mul_le_mul_of_nonneg_left (hp1 e) (hp0 e),
        sq_nonneg (p e)]
    simp only [hω, if_true]
    nlinarith [hc]
  · have hc : (p e) ^ 2 ≤ 1 := by
      nlinarith [hp0 e, hp1 e, mul_le_mul_of_nonneg_left (hp1 e) (hp0 e)]
    rw [if_neg hω, zero_sub]
    have hnorm : (-(p e)) ^ 2 = (p e) ^ 2 := by
      rw [pow_two, pow_two, neg_mul_neg]
    rw [hnorm]
    linarith

/-- The `h_meas` clause of `matrix_hoeffding` at the design: every
summand factors through its own coordinate, so it is strongly measurable
at the `Matrix.L2OpNorm` topology. -/
theorem stronglyMeasurable_perturbSummand (e : V × V) :
    StronglyMeasurable fun ω : (V × V) → Bool => perturbSummand A p e ω :=
  stronglyMeasurable_coord_matrix
    (F := fun b => ((if b then (1 : ℝ) else 0) - p e) • perturbEdgeLap A e) e

/-- The `h_indep` clause of `matrix_hoeffding` at the design: distinct
ordered pairs are independent under the product-Bernoulli measure. -/
theorem indepFun_perturbSummand (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (e e' : V × V) (hee : e ≠ e') :
    IndepFun (fun ω : (V × V) → Bool => perturbSummand A p e ω)
      (fun ω : (V × V) → Bool => perturbSummand A p e' ω)
      (bernPMF p hp0 hp1).toMeasure :=
  indepFun_coord_matrix p hp0 hp1
    (F := fun b => ((if b then (1 : ℝ) else 0) - p e) • perturbEdgeLap A e)
    (G := fun b => ((if b then (1 : ℝ) else 0) - p e') • perturbEdgeLap A e') hee

end Design

end SpectralGraphTheory
