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
     squares of symmetric matrices are positive semidefinite);
   4. the weight-space perturbation `perturbWeight` (the summed centered
      single-edge adjacencies, with its entry formulas) and the packaging
      identity `laplacian (perturbWeight A p ω) = ∑ₑ perturbSummand A p e ω`
      — the deterministic hinge of the concentration → subspace-stability
      pipeline (`Derived/EdgePerturbationDrift.lean`), joining the
      graph-level perturbation to the Laplacian-level blocks the tail
      controls — plus the nonnegativity design condition
      (`perturbWeight_entry_nonneg`: at `p e + p eᵀ ≤ 1` every resampled
      entry is nonnegative at every outcome — the admissibility
      dissolution's nonnegativity half);
  5. the degree-deviation design (`degPerturbWeight`/`degPerturbSummand`
      and the identity `deg_resampled`) with every hypothesis clause of
      the *scalar* `hoeffding_inequality` axiom proved at the design
      (measurability, pairwise independence, the bound `|X_e| ≤ |w_v(e)|`,
      and the centering `∫ X_e = 0` through the Bernoulli mean) — the
      engine of the scalar axiom's first theorem consumer, the
      per-vertex degree tail — together with the second-moment clause
      for the *Bernstein* twin (`integral_sq_degPerturbSummand`: the
      variance integral `∫ X_e² = w_v(e)² p e (1 − p e)` through
      BernoulliProduct's `integral_sq_delta_sub`), the engine of
      `bernstein_inequality`'s and `bernstein_bounded_variance`'s first
      theorem consumers.

  The axiom-backed tail theorems live in `Scaffold/Derived/
  EdgePerturbationTail.lean`; the concentration → subspace-stability
  pipeline (the composed high-probability Fiedler drift) in
  `Scaffold/Derived/EdgePerturbationDrift.lean`; QA in
  `Scaffold/QA/Derived/EdgePerturbation_QA.lean`.
-/

import Scaffold.Mathlib.GraphTheory.Sparsification
import Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Mathlib.LinearAlgebra.Matrix.PosDef

open MeasureTheory ProbabilityTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open Scaffold.Mathlib.Probability.Concentration.Scalar
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

/-- The repaired `h_indep` clause of `matrix_hoeffding` at the design,
transported to the axiom's `Fin n` index: the whole summand family is
mutually independent under the product-Bernoulli measure (the pairwise
lemma above is its two-point consequence, kept for the refutation
records). -/
theorem iIndepFun_perturbSummand (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) :
    iIndepFun (fun _ : Fin (Fintype.card (V × V)) =>
        (inferInstance : MeasurableSpace (Matrix V V ℝ)))
      (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
        perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω)
      (bernPMF p hp0 hp1).toMeasure :=
  iIndepFun_coord_matrix p hp0 hp1 (Fintype.equivFin (V × V)).symm
    ((Fintype.equivFin (V × V)).symm.injective)
    (fun k b => ((if b then (1 : ℝ) else 0) - p ((Fintype.equivFin (V × V)).symm k)) •
      perturbEdgeLap A ((Fintype.equivFin (V × V)).symm k))

/-- The repaired `h_mean` clause of `matrix_hoeffding` at the design (the
2026-08-30 centering repair, Errata §9): every Laplacian-side summand
integrates to zero, through the Bernoulli mean (`integral_delta`) and the
audit's integrability safety (`integrable_of_bounded_measurable`) — the
matrix-codomain clone of `integral_degPerturbSummand_eq_zero` below. The
centering is what the semidefinite domination clause cannot see: the
refuting family of the pre-repair axiom is a *constant* multiple of the
design's edge block (mean `≠ 0`), so this clause is the repair's
load-bearing content at the consumer. -/
theorem integral_perturbSummand_eq_zero (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (e : V × V) :
    ∫ ω : (V × V) → Bool, perturbSummand A p e ω
      ∂(bernPMF p hp0 hp1).toMeasure = 0 := by
  have hδmeas : Measurable
      fun ω : (V × V) → Bool => (if ω e then (1 : ℝ) else 0) :=
    (measurable_of_finite
      (fun b : Bool => if b then (1 : ℝ) else 0)).comp (measurable_coord e)
  have hintf : Integrable
      (fun ω : (V × V) → Bool => (if ω e then (1 : ℝ) else 0))
      (bernPMF p hp0 hp1).toMeasure := by
    refine integrable_of_bounded_measurable hδmeas (a := (1 : ℝ)) ?_
    intro ω
    cases h : ω e <;> simp [h]
  have hfun : (fun ω : (V × V) → Bool => perturbSummand A p e ω)
      = fun ω : (V × V) → Bool =>
        ((if ω e then (1 : ℝ) else 0) - p e) • perturbEdgeLap A e := by
    funext ω
    rfl
  rw [hfun, integral_smul_const]
  have hdecomp := integral_sub
    (f := fun ω : (V × V) → Bool => (if ω e then (1 : ℝ) else 0))
    (g := fun _ : (V × V) → Bool => p e) hintf (integrable_const _)
  rw [hdecomp, integral_delta]
  have hconst : ∫ (_ : (V × V) → Bool), p e ∂(bernPMF p hp0 hp1).toMeasure
      = p e := by
    rw [integral_const]
    simp
  rw [hconst, sub_self, zero_smul]

end Design

/-! ## 4. The weight-space perturbation and the packaging identity -/

section WeightSpace

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- The single-edge *adjacency* summand of the design: the centered
Bernoulli coefficient times the single-edge graph. -/
def perturbAdj (A : WAdj (V := V)) (p : (V × V) → ℝ) (e : V × V)
    (ω : (V × V) → Bool) : Matrix V V ℝ :=
  ((if ω e then (1 : ℝ) else 0) - p e) • edgeAdj e.1 e.2 (A e.1 e.2)

omit [Fintype V] in
theorem perturbAdj_isSymm (A : WAdj (V := V)) (p : (V × V) → ℝ) (e : V × V)
    (ω : (V × V) → Bool) : (perturbAdj A p e ω).IsSymm := by
  show (perturbAdj A p e ω)ᵀ = perturbAdj A p e ω
  rw [perturbAdj, Matrix.transpose_smul]
  exact congrArg (((if ω e then (1 : ℝ) else 0) - p e) • ·)
    (edgeAdj_isSymm e.1 e.2 (A e.1 e.2)).eq

/-- **The random weight-space perturbation** of the design: the summed
centered single-edge adjacencies. Its Laplacian is exactly the summed
centered edge-Laplacian blocks the tail controls
(`laplacian_perturbWeight`) — the bridge through which graph-level
consumers (the Fiedler-line drift theorem) read the tail's norm bound as
a perturbation of the Laplacian operator. -/
def perturbWeight (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (ω : (V × V) → Bool) : Matrix V V ℝ :=
  ∑ e : V × V, perturbAdj A p e ω

theorem perturbWeight_isSymm (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (ω : (V × V) → Bool) : (perturbWeight A p ω).IsSymm := by
  show (perturbWeight A p ω)ᵀ = perturbWeight A p ω
  rw [perturbWeight, Matrix.transpose_sum]
  exact Finset.sum_congr rfl
    fun e _ => (perturbAdj_isSymm A p e ω).eq

/-- **The entry formula of the weight-space perturbation, off the
diagonal**: only the two ordered pairs on `{i, j}` contribute. -/
theorem perturbWeight_apply_of_ne (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (ω : (V × V) → Bool) {i j : V} (hij : i ≠ j) :
    perturbWeight A p ω i j
      = ((if ω (i, j) then (1 : ℝ) else 0) - p (i, j)) * A i j
        + ((if ω (j, i) then (1 : ℝ) else 0) - p (j, i)) * A j i := by
  classical
  have hterm : ∀ e : V × V, (perturbAdj A p e ω) i j
      = if e = (i, j) then ((if ω (i, j) then (1 : ℝ) else 0) - p (i, j)) * A i j
        else if e = (j, i) then ((if ω (j, i) then (1 : ℝ) else 0) - p (j, i)) * A j i
        else 0 := by
    intro e
    unfold perturbAdj
    by_cases h1 : e = (i, j)
    · subst h1
      have hee : edgeAdj i j (A i j) i j = A i j := by
        rw [edgeAdj_apply]; simp
      simp only [Matrix.smul_apply, smul_eq_mul, hee]
      simp
    · by_cases h2 : e = (j, i)
      · subst h2
        have hee : edgeAdj j i (A j i) i j = A j i := by
          rw [edgeAdj_apply]; simp [hij]
        simp only [Matrix.smul_apply, smul_eq_mul, hee]
        simp [hij, Ne.symm hij]
      · simp only [Matrix.smul_apply, smul_eq_mul, edgeAdj_apply]
        rw [if_neg (fun h : i = e.1 ∧ j = e.2 => h1 (Prod.ext h.1.symm h.2.symm)),
            if_neg (fun h : i = e.2 ∧ j = e.1 => h2 (Prod.ext h.2.symm h.1.symm)),
            mul_zero, if_neg h1, if_neg h2]
  have hcoll : ∑ e ∈ (Finset.univ : Finset (V × V)), perturbAdj A p e ω i j
      = ∑ e ∈ ({(i, j), (j, i)} : Finset (V × V)), perturbAdj A p e ω i j := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro e _ he
    rw [Finset.mem_insert, Finset.mem_singleton] at he
    rw [hterm e, if_neg (fun h => he (Or.inl h)),
      if_neg (fun h => he (Or.inr h))]
  rw [perturbWeight, Matrix.sum_apply, hcoll, Finset.sum_insert (by
      intro h
      simp only [Finset.mem_singleton, Prod.mk.injEq] at h
      exact hij h.1), Finset.sum_singleton, hterm (i, j), hterm (j, i)]
  have hne1 : ¬((i, j) = (j, i)) := fun h => hij (congrArg Prod.fst h)
  have hne2 : ¬((j, i) = (i, j)) := fun h => hij (congrArg Prod.fst h).symm
  simp [hne1, hne2]

/-- **The entry formula on the diagonal**: a single ordered pair
contributes (no double count). -/
theorem perturbWeight_apply_diag (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (ω : (V × V) → Bool) (i : V) :
    perturbWeight A p ω i i
      = ((if ω (i, i) then (1 : ℝ) else 0) - p (i, i)) * A i i := by
  classical
  have hterm : ∀ e : V × V, (perturbAdj A p e ω) i i
      = if e = (i, i) then ((if ω (i, i) then (1 : ℝ) else 0) - p (i, i)) * A i i
        else 0 := by
    intro e
    unfold perturbAdj
    simp only [Matrix.smul_apply, smul_eq_mul, edgeAdj_apply]
    by_cases h1 : i = e.1 ∧ i = e.2
    · have he : e = (i, i) := Prod.ext h1.1.symm h1.2.symm
      subst he
      simp
    · rw [if_neg h1, if_neg (fun h : i = e.2 ∧ i = e.1 => h1 ⟨h.2, h.1⟩),
        mul_zero]
      have hne : e ≠ (i, i) := by
        intro h
        exact h1 ⟨by rw [h], by rw [h]⟩
      rw [if_neg hne]
  have hcoll : ∑ e ∈ (Finset.univ : Finset (V × V)), perturbAdj A p e ω i i
      = ∑ e ∈ ({(i, i)} : Finset (V × V)), perturbAdj A p e ω i i := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro e _ he
    rw [hterm e]
    rw [Finset.mem_singleton] at he
    rw [if_neg he]
  rw [perturbWeight, Matrix.sum_apply, hcoll, Finset.sum_singleton,
    hterm (i, i)]
  simp

/-- **The nonnegativity design condition**: at the pair condition
`p e + p (e.2, e.1) ≤ 1` — satisfied with equality by the uniform design
`p ≡ ½`, with slack by any smaller uniform design — every resampled
entry is nonnegative at *every* outcome, so the resampled graph is a
genuine nonnegative weighted graph with no event restriction. Off the
diagonal the resampled entry is `A i j · (1 + δ_{ij} + δ_{ji} − p_{ij}
− p_{ji})` with `δ ∈ {0,1}` and the pair sum at most `1` (symmetry
identifies the two ordered contributions); on the diagonal `A i i · (1
+ δ_{ii} − p_{ii})` with `p_{ii} ≤ 1`. This dissolves the nonnegativity
half of the window family's admissibility conjunct
(`Derived/EdgePerturbationTail.lean`'s `perturbAdmissible`). -/
theorem perturbWeight_entry_nonneg (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hp1 : ∀ e, p e ≤ 1)
    (hpd : ∀ e, p e + p (e.2, e.1) ≤ 1)
    (ω : (V × V) → Bool) (i j : V) :
    0 ≤ (A + perturbWeight A p ω) i j := by
  have hdelta : ∀ e : V × V, (0 : ℝ) ≤ (if ω e then (1 : ℝ) else 0) := by
    intro e; cases h : ω e <;> simp [h]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.add_apply, perturbWeight_apply_diag]
    have hfac : (0 : ℝ)
        ≤ 1 + (if ω (i, i) then (1 : ℝ) else 0) - p (i, i) := by
      have h1 := hp1 (i, i)
      have h2 := hdelta (i, i)
      linarith
    have hEq : (A i i + ((if ω (i, i) then (1 : ℝ) else 0) - p (i, i)) * A i i)
        = A i i * (1 + (if ω (i, i) then (1 : ℝ) else 0) - p (i, i)) := by
      ring
    linarith [hEq, mul_nonneg (hnn i i) hfac]
  · rw [Matrix.add_apply, perturbWeight_apply_of_ne A p ω hij]
    have hfac : (0 : ℝ)
        ≤ 1 + (if ω (i, j) then (1 : ℝ) else 0)
          + (if ω (j, i) then (1 : ℝ) else 0) - p (i, j) - p (j, i) := by
      have h1 := hpd (i, j)
      have h2 := hdelta (i, j)
      have h3 := hdelta (j, i)
      linarith
    have hEq : (A i j + ((if ω (i, j) then (1 : ℝ) else 0) - p (i, j)) * A i j
          + ((if ω (j, i) then (1 : ℝ) else 0) - p (j, i)) * A j i)
        = A i j * (1 + (if ω (i, j) then (1 : ℝ) else 0)
          + (if ω (j, i) then (1 : ℝ) else 0) - p (i, j) - p (j, i)) := by
      rw [Matrix.IsSymm.apply hA j i]
      ring
    linarith [hEq, mul_nonneg (hnn i j) hfac]

/-- **The packaging identity**: the Laplacian of the random
weight-space perturbation is exactly the summed centered edge-Laplacian
blocks the tail controls — the concentration → stability pipeline's
deterministic hinge, through the Laplacian's linearity package
(`laplacian_sum`, `laplacian_smul`) and the single-edge join
(`laplacian_edgeAdj_eq_perturbEdgeLap`). -/
theorem laplacian_perturbWeight (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (ω : (V × V) → Bool) :
    laplacian (perturbWeight A p ω) = ∑ e : V × V, perturbSummand A p e ω := by
  rw [perturbWeight, laplacian_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [perturbAdj, laplacian_smul, laplacian_edgeAdj_eq_perturbEdgeLap]
  rfl

end WeightSpace

/-! ## 5. The degree-deviation design

The scalar-companion design of the sections above: the *degree* of the
resampled graph under the centered Bernoulli design, as a sum of
independent centered bounded real variables — the exact hypothesis shape
of the scalar `hoeffding_inequality` axiom
(`Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding`) and of
the `bernstein_inequality`/`bernstein_bounded_variance` pair
(`...Concentration.Scalar.Bernstein`). The
λ₂/norm tails of the Derived module control the *operator*
(`L(E_ω)·1 = 0` identically — they carry zero degree information); this
design is the missing complementary concentration, and every clause
lemma below is stated at the same level of generality as its matrix
sibling (sign-free: no hypothesis on the weight matrix `A`, the only
load-bearing hypothesis being the sampling interval `p ∈ [0, 1]`).

The axiom-backed tails live in `Scaffold/Derived/
EdgePerturbationTail.lean` (`edgePerturbation_degree_tail`, the scalar
axiom's first theorem consumer, and the Bernstein twin
`edgePerturbation_degree_tail_bernstein`/`_bernstein_budget`); QA in
`Scaffold/QA/Derived/EdgePerturbation_QA.lean`'s degreeTail and
bernsteinTwin sections.
-/

section DegreeDesign

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- The weight of the ordered pair `e` in vertex `v`'s degree: the
pair's adjacency weight when `v` is an endpoint, zero otherwise (at a
loop both endpoints coincide; the pair's weight counts once, exactly as
in `deg_perturbAdj`'s single contribution). -/
def degPerturbWeight (A : WAdj (V := V)) (v : V) (e : V × V) : ℝ :=
  if v = e.1 ∨ v = e.2 then A e.1 e.2 else 0

/-- The centered Bernoulli degree summand of the ordered pair `e` at
outcome `ω`: the pair's contribution to the deviation of `v`'s resampled
degree from its base degree. Centering makes the design's expected
degree deviation zero at every `p`. -/
def degPerturbSummand (A : WAdj (V := V)) (p : (V × V) → ℝ) (v : V)
    (e : V × V) (ω : (V × V) → Bool) : ℝ :=
  ((if ω e then (1 : ℝ) else 0) - p e) * degPerturbWeight A v e

theorem deg_perturbAdj (A : WAdj (V := V)) (p : (V × V) → ℝ) (e : V × V)
    (ω : (V × V) → Bool) (v : V) :
    deg (perturbAdj A p e ω) v = degPerturbSummand A p v e ω := by
  rw [perturbAdj, deg_smul, degPerturbSummand]
  simp only [deg_edgeAdj, degPerturbWeight]

theorem deg_perturbWeight (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (ω : (V × V) → Bool) (v : V) :
    deg (perturbWeight A p ω) v = ∑ e, degPerturbSummand A p v e ω := by
  rw [perturbWeight, deg_sum]
  exact Finset.sum_congr rfl fun e _ => deg_perturbAdj A p e ω v

/-- **The degree-deviation identity**: the resampled degree is the base
degree plus the summed centered Bernoulli summands — the deterministic
hinge through which the scalar tail theorem reads a degree statement.
Through the degree-linearity package (`deg_add`/`deg_sum`) and the
single-edge row sums (`deg_edgeAdj`); a wrong entry formula or row-sum
shape breaks exactly this. -/
theorem deg_resampled (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (ω : (V × V) → Bool) (v : V) :
    deg (A + perturbWeight A p ω) v
      = deg A v + ∑ e, degPerturbSummand A p v e ω := by
  rw [deg_add, deg_perturbWeight]

omit [Fintype V] in
theorem measurable_degPerturbSummand (A : WAdj (V := V))
    (p : (V × V) → ℝ) (v : V) (e : V × V) :
    Measurable fun ω : (V × V) → Bool => degPerturbSummand A p v e ω :=
  (measurable_of_finite
    (fun b : Bool => ((if b then (1 : ℝ) else 0) - p e)
      * degPerturbWeight A v e)).comp (measurable_coord e)

theorem indepFun_degPerturbSummand (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (v : V) {e e' : V × V}
    (hee : e ≠ e') :
    IndepFun (fun ω : (V × V) → Bool => degPerturbSummand A p v e ω)
      (fun ω : (V × V) → Bool => degPerturbSummand A p v e' ω)
      (bernPMF p hp0 hp1).toMeasure :=
  (indepFun_coord p hp0 hp1 hee).comp
    (measurable_of_finite
      (fun b : Bool => ((if b then (1 : ℝ) else 0) - p e)
        * degPerturbWeight A v e))
    (measurable_of_finite
      (fun b : Bool => ((if b then (1 : ℝ) else 0) - p e')
        * degPerturbWeight A v e'))

/-- The repaired `h_indep` clause of `hoeffding_inequality` at the
degree-tail design, transported to the axiom's `Fin n` index: the whole
centered-summand family is mutually independent. -/
theorem iIndepFun_degPerturbSummand (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (v : V) :
    iIndepFun (fun _ : Fin (Fintype.card (V × V)) =>
        (inferInstance : MeasurableSpace ℝ))
      (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
        degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω)
      (bernPMF p hp0 hp1).toMeasure :=
  iIndepFun_coord_apply p hp0 hp1 (Fintype.equivFin (V × V)).symm
    ((Fintype.equivFin (V × V)).symm.injective)
    (fun k b => ((if b then (1 : ℝ) else 0) - p ((Fintype.equivFin (V × V)).symm k)) *
      degPerturbWeight A v ((Fintype.equivFin (V × V)).symm k))
    (fun _ => measurable_of_finite _)

omit [Fintype V] in
/-- The `h_bound` clause of `hoeffding_inequality` at the design:
`|X_e| ≤ |w_v(e)|`, the interval `(δ_e − p_e) ∈ [−1, 1]` being the only
load-bearing input (the design is sign-free — no hypothesis on `A`). -/
theorem degPerturbSummand_abs_le (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (v : V) (e : V × V)
    (ω : (V × V) → Bool) :
    |degPerturbSummand A p v e ω| ≤ |degPerturbWeight A v e| := by
  have hp0e := hp0 e
  have hp1e := hp1 e
  have h1 : |((if ω e then (1 : ℝ) else 0) - p e)| ≤ 1 := by
    by_cases hω : ω e
    · simp only [hω, if_true]
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · rw [if_neg hω, zero_sub, abs_neg]
      exact abs_le.2 ⟨by linarith, by linarith⟩
  unfold degPerturbSummand
  rw [abs_mul]
  have hle := mul_le_mul_of_nonneg_right h1
    (abs_nonneg (degPerturbWeight A v e))
  rwa [one_mul] at hle

/-- The `h_mean` clause of `hoeffding_inequality` at the design: every
summand integrates to zero, through the Bernoulli mean
(`integral_delta`) and the audit's integrability safety
(`integrable_of_bounded_measurable`) — no `p e ≠ 0` guard needed,
unlike the sparsification design's division-based centering. -/
theorem integral_degPerturbSummand_eq_zero (A : WAdj (V := V))
    (p : (V × V) → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (v : V)
    (e : V × V) :
    ∫ ω : (V × V) → Bool, degPerturbSummand A p v e ω
      ∂(bernPMF p hp0 hp1).toMeasure = 0 := by
  have hδmeas : Measurable
      fun ω : (V × V) → Bool => (if ω e then (1 : ℝ) else 0) :=
    (measurable_of_finite
      (fun b : Bool => if b then (1 : ℝ) else 0)).comp (measurable_coord e)
  have hintf : Integrable
      (fun ω : (V × V) → Bool => (if ω e then (1 : ℝ) else 0))
      (bernPMF p hp0 hp1).toMeasure := by
    refine integrable_of_bounded_measurable hδmeas (a := (1 : ℝ)) ?_
    intro ω
    cases h : ω e <;> simp [h]
  have hfun : (fun ω : (V × V) → Bool => degPerturbSummand A p v e ω)
      = fun ω : (V × V) → Bool =>
        ((if ω e then (1 : ℝ) else 0) - p e) • degPerturbWeight A v e := by
    funext ω
    unfold degPerturbSummand
    rw [smul_eq_mul]
  rw [hfun, integral_smul_const]
  have hdecomp := integral_sub
    (f := fun ω : (V × V) → Bool => (if ω e then (1 : ℝ) else 0))
    (g := fun _ : (V × V) → Bool => p e) hintf (integrable_const _)
  rw [hdecomp, integral_delta]
  have hconst : ∫ (_ : (V × V) → Bool), p e ∂(bernPMF p hp0 hp1).toMeasure
      = p e := by
    rw [integral_const]
    simp
  rw [hconst]
  simp

/-- The variance clause of `bernstein_inequality` at the design: the
centered square of the degree summand integrates to
`w_v(e)² p e (1 − p e)` — the Bernoulli variance of the pair's indicator
scaled by the squared incident weight, through the second-moment
companion `integral_sq_delta_sub`. Together with
`integral_degPerturbSummand_eq_zero` (the centering) this identifies the
axiom's variance statistic exactly: `∑ₑ ∫ (X_e − E X_e)² = ∑ₑ
w_v(e)² p e (1 − p e)` — the quantity that makes the Bernstein twin
*variance-adaptive* (strictly sharper than the Hoeffding range statistic
`∑ₑ w_v(e)²` at interior sampling probabilities). -/
theorem integral_sq_degPerturbSummand (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) (v : V) (e : V × V) :
    ∫ ω : (V × V) → Bool, (degPerturbSummand A p v e ω) ^ 2
        ∂(bernPMF p hp0 hp1).toMeasure
      = (degPerturbWeight A v e) ^ 2 * p e * (1 - p e) := by
  have hfun : (fun ω : (V × V) → Bool => (degPerturbSummand A p v e ω) ^ 2)
      = fun ω : (V × V) → Bool =>
          (((if ω e then (1 : ℝ) else 0) - p e) ^ 2) •
            (degPerturbWeight A v e) ^ 2 := by
    funext ω
    unfold degPerturbSummand
    simp only [smul_eq_mul, sq]
    ring
  rw [hfun, integral_smul_const, integral_sq_delta_sub p hp0 hp1 e, smul_eq_mul]
  ring

end DegreeDesign

end SpectralGraphTheory
