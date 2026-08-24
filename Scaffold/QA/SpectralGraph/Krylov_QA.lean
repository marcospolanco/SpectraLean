/-
  Krylov_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Krylov` — Steps 1a (the
  interface layer), 1b (the spectral discharge), and 1c (the final
  statement) of `proposals/approximate-spectral-projection.md`: the
  Chebyshev band bound, the two priced shallow gaps (`natDegree T`,
  the growth lemma), the `sum_mulVec` push, the polynomial-eigenaction
  transfer, Krylov-span membership, the composite's spectral discharge,
  and the final `kanielPaige` statement — instantiated on `Fin 2`/`Fin
  3` fixtures, each numeric value pinned raw (independent of the
  theorem it checks), with a degree-guard refutation, a full
  hypothesis-form instantiation of the Kaniel–Paige skeleton on a
  diagonal fixture, the `k = 1` degenerate case, the `b = u` tightness
  witness, and the simple-top guard refuted on a top-multiplicity
  fixture.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Krylov
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

open Polynomial SpectralGraphTheory

namespace SpectralGraphTheory.QA

/-!
## Fixtures
-/

/-- The flip matrix `[[0,1],[1,0]]`: symmetric, `M² = 1`, and `M` swaps
the coordinates — so its Krylov spans from `e₁` are exactly the
coordinate spans (the line at `k = 1`, everything at `k = 2`). -/
def flipAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- The diagonal fixture `diag(2, 0)`: top eigenvalue `2` at `e₁`,
bottom eigenvalue `0` at `e₂` — every spectral-layer hypothesis of the
skeleton is decidable arithmetic on it. -/
def diagM : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 0; 0, 0]

/-- The balanced starting vector `b = ½(e₁ + e₂)`. -/
noncomputable def bvec : Fin 2 → ℝ :=
  ![1/2, 1/2]

/-- Fixture fact: the flip swaps the coordinates, so `M e₁ = e₂`. -/
theorem flipAdj_mulVec_e1_raw_QA :
    flipAdj *ᵥ (![1, 0] : Fin 2 → ℝ) = ![0, 1] := by
  funext i
  fin_cases i <;>
    simp [flipAdj, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-!
## The Chebyshev layer
-/

/-- Raw pin: `T₂(0) = -1` (from the pin's `T_two`), the band bound's
boundary equality case at an endpoint of `[-1, 1]`. -/
theorem cheb_T2_eval_zero_raw_QA :
    (Polynomial.Chebyshev.T ℝ 2).eval 0 = -1 := by
  rw [Polynomial.Chebyshev.T_two]
  norm_num [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- Raw pin: `T₃(1/2) = -1` (unfolded through the two-step recurrence
and `T_two`), the band bound's equality case at a *strictly interior*
point — `|T₃|` touches `1` inside `(-1, 1)`, so the bound is sharp
there, not just at the endpoints. -/
theorem cheb_T3_eval_half_raw_QA :
    (Polynomial.Chebyshev.T ℝ 3).eval (1/2) = -1 := by
  have hC2 : (2 : ℝ[X]) = Polynomial.C (2 : ℝ) := (map_ofNat _ 2).symm
  rw [show (3 : ℤ) = (1 : ℤ) + 2 from by norm_num,
    Polynomial.Chebyshev.T_add_two, show (1 : ℤ) + 1 = 2 from by norm_num,
    Polynomial.Chebyshev.T_two, hC2,
    Polynomial.Chebyshev.T_one]
  norm_num [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]

/-- Raw pin: `T₂(1/4) = -7/8`, a strictly-interior point with
`|T₂| < 1` — the generic (non-sharp) behavior of the band bound. -/
theorem cheb_T2_band_strict_raw_QA :
    (Polynomial.Chebyshev.T ℝ ((2 : ℕ) : ℤ)).eval (1/4) = -7/8 := by
  push_cast
  rw [Polynomial.Chebyshev.T_two]
  norm_num [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- The band bound instantiated at the interior point, its value
supplied by the raw pin above: `7/8 ≤ 1` through the delivered
theorem. -/
theorem cheb_band_instantiated_QA :
    (7/8 : ℝ) ≤ 1 := by
  have h := abs_T_eval_le_one 2
    (show -1 ≤ (1/4 : ℝ) by norm_num) (by norm_num)
  rw [cheb_T2_band_strict_raw_QA, abs_of_neg (by norm_num)] at h
  linarith

/-- The first priced gap instantiated: `natDegree (T ℝ 5) = 5` —
the degree grows with the index (the `hdeg : natDegree < k` side
condition consumes exactly this), including the degenerate base. -/
theorem cheb_natDegree_instances_QA :
    (Polynomial.Chebyshev.T ℝ 5).natDegree = 5 ∧
      (Polynomial.Chebyshev.T ℝ 0).natDegree = 0 :=
  ⟨natDegree_T 5, natDegree_T 0⟩

/-- The second priced gap, two routes meeting: `1 ≤ T₂(2)` from the
delivered growth lemma, and `T₂(2) = 7` raw — the lemma's bound is
strictly exceeded at an interior `x > 1`, so `1 ≤ T` is genuine growth,
not a degenerate constant. -/
theorem cheb_growth_two_routes_QA :
    1 ≤ (Polynomial.Chebyshev.T ℝ 2).eval 2 ∧
      (Polynomial.Chebyshev.T ℝ 2).eval 2 = 7 := by
  refine ⟨one_le_eval_T_of_one_le (by norm_num : (1:ℝ) ≤ 2) 2, ?_⟩
  rw [Polynomial.Chebyshev.T_two]
  norm_num [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-!
## The `sum_mulVec` push
-/

/-- The push instantiated on concrete matrices: the sum of a
two-matrix family acts on `![1,-1]` as the sum of the individual
actions, both sides ground arithmetic (`![3,4] *ᵥ ![1,-1] = ![-1,-1]`,
`![0,1;1,0] *ᵥ ![1,-1] = ![-1,1]`, total `![-2,0]`). -/
theorem sum_mulVec_QA :
    (∑ i ∈ (Finset.univ : Finset (Fin 2)),
        (![!![1, 2; 3, 4], flipAdj] : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) i)
      *ᵥ (![1, -1] : Fin 2 → ℝ)
      = ![-2, 0] := by
  have hA : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ)
      *ᵥ (![1, -1] : Fin 2 → ℝ) = ![-1, -1] := by
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have hB : flipAdj *ᵥ (![1, -1] : Fin 2 → ℝ) = ![-1, 1] := by
    funext i
    fin_cases i <;>
      norm_num [flipAdj, Matrix.mulVec, Matrix.dotProduct,
        Fin.sum_univ_two]
  have h0 : (![!![1, 2; 3, 4], flipAdj] :
      Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) 0 = !![1, 2; 3, 4] := rfl
  have h1 : (![!![1, 2; 3, 4], flipAdj] :
      Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) 1 = flipAdj := rfl
  rw [sum_mulVec, Fin.sum_univ_two, h0, h1, hA, hB]
  funext i
  fin_cases i <;> norm_num [Pi.add_apply]

/-!
## Polynomial action on eigenvectors (two routes + annihilator)
-/

theorem diagM_eigenvector_raw_QA :
    diagM *ᵥ (![1, 0] : Fin 2 → ℝ) = (2 : ℝ) • (![1, 0] : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [diagM, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- Theorem route: `(X² + 1)(diagM)` acts on `e₁` as `p(2) • e₁ =
5 • e₁`. -/
theorem aeval_action_theorem_QA :
    (aeval diagM ((X ^ 2 + C 1 : ℝ[X]))) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (![5, 0] : Fin 2 → ℝ) := by
  have h := aeval_mulVec_eq_eval_smul diagM diagM_eigenvector_raw_QA
    ((X ^ 2 + C 1 : ℝ[X]))
  rw [h]
  funext i
  fin_cases i <;>
    norm_num [Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Pi.smul_apply, smul_eq_mul]

set_option linter.unnecessarySeqFocus false in
/-- Raw route to the same value, independent of the transfer theorem:
`aeval diagM (X² + 1) = diagM² + 1 = !![5, 0; 0, 1]` computed by hand,
then the literal action on `e₁`. -/
theorem aeval_action_raw_QA :
    (aeval diagM ((X ^ 2 + C 1 : ℝ[X]))) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (![5, 0] : Fin 2 → ℝ) := by
  have h1 : aeval diagM ((X ^ 2 + C 1 : ℝ[X]))
      = diagM ^ 2 + 1 := by
    simp [map_add, map_pow, aeval_X, map_one]
  have h2 : diagM ^ 2 = !![4, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagM, pow_two, Matrix.mul_apply] <;> ring
  rw [h1, h2, Matrix.add_mulVec, Matrix.one_mulVec]
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-- The annihilator witness: `(X − 2)(diagM)` kills `e₁` — the
eigenvalue shifted into the polynomial turns the scalar action to
`0 • e₁`. -/
theorem aeval_annihilator_QA :
    (aeval diagM ((X - C (2 : ℝ) : ℝ[X]))) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (0 : Fin 2 → ℝ) := by
  have h := aeval_mulVec_eq_eval_smul diagM diagM_eigenvector_raw_QA
    ((X - C (2 : ℝ) : ℝ[X]))
  rw [h, show ((X - C (2 : ℝ) : ℝ[X]).eval 2) = 0 from by
    norm_num [Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]]
  simp

/-!
## Krylov-span membership (two routes, composed use, guard refuted)
-/

/-- Theorem route: `e₂ = M e₁` is the degree-1 polynomial image of
`e₁`, so it lies in `krylovSpan M e₁ 2` — membership through the
polynomial interface. -/
theorem krylov_membership_theorem_QA :
    (![0, 1] : Fin 2 → ℝ) ∈ krylovSpan flipAdj (![1, 0] : Fin 2 → ℝ) 2 := by
  have h := aeval_mulVec_mem_krylovSpan flipAdj (![1, 0] : Fin 2 → ℝ) 2 X
    (by
      rw [Polynomial.natDegree_X]
      norm_num)
  rwa [aeval_X, flipAdj_mulVec_e1_raw_QA] at h

/-- Raw route to the same membership: `e₂` is literally the `i = 1`
generator of the span, no polynomial interface involved. -/
theorem krylov_membership_generator_QA :
    (![0, 1] : Fin 2 → ℝ) ∈ krylovSpan flipAdj (![1, 0] : Fin 2 → ℝ) 2 := by
  refine Submodule.subset_span (Set.mem_range.mpr ⟨1, ?_⟩)
  simp only [Fin.val_one, pow_one]
  exact flipAdj_mulVec_e1_raw_QA

/-- The composed use of the first priced gap — exactly the consumption
pattern Step 1b needs: the degree-5 Chebyshev polynomial's image of
`e₁` lies in the 6-th Krylov span, `hdeg` discharged by `natDegree_T`
alone. -/
theorem krylov_T5_composed_membership_QA :
    (aeval flipAdj (Polynomial.Chebyshev.T ℝ ((5 : ℕ) : ℤ)))
      *ᵥ (![1, 0] : Fin 2 → ℝ)
      ∈ krylovSpan flipAdj (![1, 0] : Fin 2 → ℝ) 6 :=
  aeval_mulVec_mem_krylovSpan _ _ _ _ (by
    rw [natDegree_T 5]
    norm_num)

/-- **The degree guard refuted**: the hypothesis-free membership form
is *false* — the same degree-1 polynomial image `M e₁ = e₂` provably
does **not** lie in `krylovSpan M e₁ 1` (the line `ℝ · e₁`), since
membership there forces the second coordinate to vanish. `hdeg` is
load-bearing, not decoration. -/
theorem krylov_degree_guard_refuted_QA :
    ¬ ((aeval flipAdj (X : ℝ[X])) *ᵥ (![1, 0] : Fin 2 → ℝ)
        ∈ krylovSpan flipAdj (![1, 0] : Fin 2 → ℝ) 1) := by
  intro hmem
  -- the Fin 1-indexed range collapses to the single generator e₁
  have hrange : Set.range (fun i : Fin 1 =>
      (flipAdj ^ (i : ℕ)) *ᵥ (![1, 0] : Fin 2 → ℝ)) = {![1, 0]} := by
    ext z
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      simp only [pow_zero, Matrix.one_mulVec] at hi
      exact hi.symm
    · rintro rfl
      exact ⟨0, by simp [pow_zero, Matrix.one_mulVec]⟩
  rw [krylovSpan, hrange, Submodule.mem_span_singleton] at hmem
  obtain ⟨r, hr⟩ := hmem
  rw [aeval_X, flipAdj_mulVec_e1_raw_QA] at hr
  -- r • e₁ = e₂: the second coordinate kills it
  have hcoord : (r • (![1, 0] : Fin 2 → ℝ)) 1
      = (![0, 1] : Fin 2 → ℝ) 1 := congrFun hr 1
  norm_num [Pi.smul_apply, smul_eq_mul] at hcoord

/-!
## The Kaniel–Paige skeleton instantiated
-/

/-- The skeleton's bound constant on the diagonal fixture,
`k = 1`, `p = 1`, `c = s = 1/2`, `Ltop = 2`, `Lbot = 0`, `Tv = 1`:
`(2 - 0) · (1/2)² / (1/2)² / 1² = 2` — the hypothesis-form conclusion
is a concrete number. -/
theorem kanielPaige_diag_bound_is_two_QA :
    (2 - 0) * (1/2) ^ 2 / (1/2) ^ 2 / (1 : ℝ) ^ 2 = 2 := by
  norm_num

/-- The Rayleigh value the instantiated bound bounds: on the diagonal
fixture, `R(diagM, b) = 1` computed raw from the definitions (the
`2/4` entry against the `1/2` norm) — the hidden witness of the
skeleton at `p = 1` *is* `b` itself (`aeval M 1 *ᵥ b = b`), and its
gap to `Ltop = 2` is exactly `1`. -/
theorem rayleigh_diagM_bvec_raw_QA :
    rayleigh diagM bvec = 1 := by
  have hne : bvec ≠ 0 := by
    intro h0
    have : bvec 0 = (0 : Fin 2 → ℝ) 0 := congrFun h0 0
    simp [bvec] at this
  rw [rayleigh, if_neg hne, quadForm]
  norm_num [diagM, bvec, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_two]

/-- **The full skeleton instantiation on the diagonal fixture**: every
hypothesis — the decomposition, the top eigenvector equation, the unit
norm, and all five named spectral-layer discharge sites (`hp₁`, `horth`,
`horthM`, `hbottom`, `hband`) — is discharged by hand arithmetic, and
the conclusion is a membership-plus-nonzero-plus-bound package. With
`kanielPaige_diag_bound_is_two_QA` and
`rayleigh_diagM_bvec_raw_QA`, the instantiated bound reads
`2 - 1 = 1 ≤ 2`: the interface contract is satisfiable and its
conclusion is non-vacuous. -/
theorem kanielPaige_skeleton_diag_QA :
    ∃ x ∈ krylovSpan diagM bvec 1, x ≠ 0 ∧
      2 - rayleigh diagM x
        ≤ (2 - 0) * (1/2) ^ 2 / (1/2) ^ 2 / (1 : ℝ) ^ 2 :=
  kanielPaigeSkeleton diagM bvec ![1, 0] ![0, 1] (1/2) (1/2) 2 0 1 1 1
    (by
      funext i
      fin_cases i <;> simp [bvec])
    (by
      funext i
      fin_cases i <;>
        simp [diagM, Matrix.mulVec, Matrix.dotProduct,
          Fin.sum_univ_two])
    (by simp [Matrix.dotProduct, Fin.sum_univ_two])
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by simp)
    (by simp)
    (by
      simp only [map_one, Matrix.one_mulVec, Matrix.dotProduct,
        Fin.sum_univ_two]
      norm_num)
    (by
      simp only [map_one, Matrix.one_mulVec, Matrix.mulVec,
        Matrix.dotProduct, diagM, Fin.sum_univ_two, Pi.zero_apply]
      norm_num)
    (by
      simp only [map_one, Matrix.one_mulVec, Matrix.mulVec,
        Matrix.dotProduct, diagM, Fin.sum_univ_two, Pi.zero_apply]
      norm_num)
    (by
      simp only [map_one, Matrix.one_mulVec, Matrix.dotProduct,
        Fin.sum_univ_two]
      norm_num)

/-!
## Step 1b: the spectral discharge
-/

/-- Fixture fact: `diagM` is symmetric — the transfer layer's one
structural hypothesis. -/
theorem diagM_symm_QA : diagM.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, diagM]

/-- The band map pins on the band `[0, 1]`, theorem route: `w(0) = -1`,
`w(1) = 1` (the band endpoints land at the Chebyshev band endpoints),
and the degree is `1` (the affine side of `hdeg`). -/
theorem bandMap_pins_theorem_QA :
    (bandMap (1:ℝ) 0).eval 0 = -1 ∧ (bandMap (1:ℝ) 0).eval 1 = 1 ∧
      (bandMap (1:ℝ) 0).natDegree = 1 :=
  ⟨bandMap_eval_bot (by norm_num), bandMap_eval_two (by norm_num),
    natDegree_bandMap (by norm_num)⟩

/-- Raw route to the same pins, independent of the band-map theorems:
`w = C 2 * (X - C (1/2))` evaluated by hand as the closed form
`w(μ) = 2μ - 1`, then the two endpoint values. -/
theorem bandMap_closed_form_raw_QA :
    (∀ μ : ℝ, (bandMap (1:ℝ) 0).eval μ = 2 * μ - 1) ∧
      (bandMap (1:ℝ) 0).eval 0 = -1 ∧ (bandMap (1:ℝ) 0).eval 1 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ
    simp only [bandMap, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_sub]
    ring
  all_goals norm_num [bandMap, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_sub]

/-- The growth pin, composed: `1 ≤ w(3) = 5` — the band-map value above
the band top is genuine growth (the `hTv` route at the composite's
data). -/
theorem bandMap_growth_composed_QA :
    1 ≤ (bandMap (1:ℝ) 0).eval 3 ∧ (bandMap (1:ℝ) 0).eval 3 = 5 := by
  refine ⟨one_le_bandMap_eval (by norm_num) (by norm_num), ?_⟩
  rw [(bandMap_closed_form_raw_QA.1 3)]
  norm_num

/-- **The self-adjointness transfer, two routes to one value**: at the
eigenvector `e₁` of `diagM` (eigenvalue `2`) and `y = ![3, -5]`, both
the delivered theorem and raw arithmetic give
`e₁ ⬝ᵥ (M y) = 6 = 2 · (e₁ ⬝ᵥ y)`. -/
theorem eigvec_transfer_theorem_QA :
    Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
        (diagM *ᵥ (![3, -5] : Fin 2 → ℝ)) = 6 := by
  rw [eigvec_dotProduct_mulVec diagM_symm_QA
    diagM_eigenvector_raw_QA (![3, -5] : Fin 2 → ℝ)]
  have : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ (![3, -5] : Fin 2 → ℝ) = 3 := by
    norm_num [Matrix.dotProduct, Fin.sum_univ_two]
  rw [this]
  norm_num

/-- Raw route: `M *ᵥ ![3,-5] = ![6, 0]` by hand, then `e₁ ⬝ᵥ ![6, 0] =
6` — independent of the transfer theorem. -/
theorem eigvec_transfer_raw_QA :
    Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
        (diagM *ᵥ (![3, -5] : Fin 2 → ℝ)) = 6 := by
  have hM : diagM *ᵥ (![3, -5] : Fin 2 → ℝ) = (![6, 0] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;>
      norm_num [diagM, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  rw [hM]
  norm_num [Matrix.dotProduct, Fin.sum_univ_two]

/-- **The polynomial transfer, theorem route**: at the same eigenvector
and `g = ![1, -1]`, `e₁ ⬝ᵥ (p(M) g) = (e₁ ⬝ᵥ g) · p(2) = 1 · 5 = 5`
for `p = X² + 1`. -/
theorem eigvec_polyTransfer_theorem_QA :
    Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
        ((aeval diagM ((X ^ 2 + C 1 : ℝ[X]))) *ᵥ (![1, -1] : Fin 2 → ℝ))
      = 5 := by
  rw [eigvec_dotProduct_aeval_mulVec diagM_symm_QA
    diagM_eigenvector_raw_QA ((X ^ 2 + C 1 : ℝ[X])) (![1, -1] : Fin 2 → ℝ)]
  have h1 : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ (![1, -1] : Fin 2 → ℝ) = 1 := by
    norm_num [Matrix.dotProduct, Fin.sum_univ_two]
  rw [h1]
  norm_num [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]

set_option linter.unnecessarySeqFocus false in
/-- Raw route to the same value: `p(M) = diagM² + 1 = !![5, 0; 0, 1]`
by hand, `p(M) ![1,-1] = ![5, -1]`, `e₁ ⬝ᵥ ![5, -1] = 5`. -/
theorem eigvec_polyTransfer_raw_QA :
    Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
        ((aeval diagM ((X ^ 2 + C 1 : ℝ[X]))) *ᵥ (![1, -1] : Fin 2 → ℝ))
      = 5 := by
  have h1 : aeval diagM ((X ^ 2 + C 1 : ℝ[X])) = diagM ^ 2 + 1 := by
    simp [map_add, map_pow, aeval_X, map_one]
  have h2 : diagM ^ 2 = !![4, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagM, pow_two, Matrix.mul_apply] <;> ring
  rw [h1, h2, Matrix.add_mulVec, Matrix.one_mulVec]
  norm_num [diagM, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-! ### The diagonal 3×3 fixture and the composite

`Fin 3` cons-literals resist simp's index-2 reduction and `fin_cases`
indices resist `rfl` (both recorded house traps), so the 3×3 fixtures
are entrywise-encoded — `Matrix.diagonal` for the matrix, if-forms for
the vectors — which reduces at every `fin_cases` literal.
-/

/-- The 3×3 diagonal fixture `diag(3, 1, 0)`: top eigenvalue `3` at
`e₁`, band `[0, 1]` below it — the smallest fixture where the band map,
the dichotomy, and the composite all carry nondegenerate content. -/
def diag310 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun j => if j = 0 then 3 else if j = 1 then 1 else 0

/-- The top-eigenvalue direction `e₁`, entrywise. -/
def u310 : Fin 3 → ℝ := fun j => if j = 0 then 1 else 0

/-- The band direction `e₂`, entrywise. -/
def g310 : Fin 3 → ℝ := fun j => if j = 1 then 1 else 0

/-- The starting vector `b = (3 e₁ + 4 e₂)/5`, unit norm with
nonzero components on both the top eigenvector and the band. -/
noncomputable def bvec310 : Fin 3 → ℝ :=
  fun j => if j = 0 then 3/5 else if j = 1 then 4/5 else 0

/-- The raw-route Krylov witness `x = p(M) b = ![3, 4/5, 0]`,
entrywise. -/
noncomputable def xraw310 : Fin 3 → ℝ :=
  fun j => if j = 0 then 3 else if j = 1 then 4/5 else 0

theorem diag310_symm : diag310.IsSymm := by
  show diag310ᵀ = diag310
  exact Matrix.diagonal_transpose _

theorem diag310_mulVec_u310_raw_QA :
    diag310 *ᵥ u310 = (3 : ℝ) • u310 := by
  funext i
  fin_cases i <;>
    simp [diag310, u310, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]

/-- **The band hypothesis discharged on the fixture** — the composite's
one eigenbasis-level input, here proved from the eigen-equation alone:
any eigenvector of `diag310` at an eigenvalue outside the band `[0, 1]`
is a multiple of `e₁`. Out-of-band below (`μ < 0`) is vacuous (the
coordinates force the zero vector against unit norm); out-of-band above
(`1 < μ`) forces the `e₂`/`e₃` coordinates to vanish. -/
theorem diag310_hpar_QA (i : Fin 3)
    (hnb : ¬(0 ≤ eigvalOf diag310 diag310_symm i ∧
      eigvalOf diag310 diag310_symm i ≤ 1)) :
    ∃ t : ℝ, eigvecOf diag310 diag310_symm i = t • u310 := by
  set μ : ℝ := eigvalOf diag310 diag310_symm i with hμ
  set v : Fin 3 → ℝ := eigvecOf diag310 diag310_symm i with hv
  have hev : diag310 *ᵥ v = μ • v := by
    have h0 : diag310 *ᵥ (eigvecOf diag310 diag310_symm i)
        = (eigvalOf diag310 diag310_symm i) • (eigvecOf diag310 diag310_symm i) :=
      (isHermitian_of_isSymm diag310_symm).mulVec_eigenvectorBasis i
    rw [← hv, ← hμ] at h0
    exact h0
  have hc0 : (3 : ℝ) * v 0 = μ * v 0 := by
    simpa [diag310, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] using congrFun hev 0
  have hc1 : v 1 = μ * v 1 := by
    simpa [diag310, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] using congrFun hev 1
  have hc2 : (0 : ℝ) = μ * v 2 := by
    simpa [diag310, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] using congrFun hev 2
  have hvv : v ⬝ᵥ v = 1 := by
    have h := eigvecOf_inner diag310 diag310_symm i i
    rw [← hv] at h
    simpa [Matrix.dotProduct] using h
  rcases not_and_or.1 hnb with h0 | h1
  · have hμlt : μ < 0 := not_le.1 h0
    have hv2 : v 2 = 0 := by
      rcases mul_eq_zero.1 hc2.symm with h | h
      · exact absurd h (ne_of_lt hμlt)
      · exact h
    have hv1 : v 1 = 0 := by
      have hkey : v 1 * (1 - μ) = 0 := by linear_combination hc1
      rcases mul_eq_zero.1 hkey with h | h
      · exact h
      · linarith
    have hv0 : v 0 = 0 := by
      have hkey : v 0 * (3 - μ) = 0 := by linear_combination hc0
      rcases mul_eq_zero.1 hkey with h | h
      · exact h
      · linarith
    have hvz : v = 0 := by
      funext j
      fin_cases j <;> simp [hv0, hv1, hv2]
    rw [hvz] at hvv
    simp at hvv
  · have hμgt : 1 < μ := not_le.1 h1
    have hμpos : (0:ℝ) < μ := by linarith
    have hv2 : v 2 = 0 := by
      rcases mul_eq_zero.1 hc2.symm with h | h
      · exact absurd h (ne_of_gt hμpos)
      · exact h
    have hv1 : v 1 = 0 := by
      have hkey : v 1 * (1 - μ) = 0 := by linear_combination hc1
      rcases mul_eq_zero.1 hkey with h | h
      · exact h
      · linarith
    refine ⟨v 0, ?_⟩
    funext j
    fin_cases j <;> simp [hv1, hv2, u310, Pi.smul_apply, smul_eq_mul]

/-- The composite band-polynomial value on the fixture data: at
`k = 2`, `T_{k-1} ∘ w` evaluated at the top eigenvalue `3` is
`T₁(w(3)) = T₁(5) = 5`. -/
theorem diag310_chebPoly_value_QA :
    ((Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).comp
        (bandMap (1:ℝ) 0)).eval 3 = 5 := by
  have hcast : (((2 - 1 : ℕ) : ℤ)) = 1 := by norm_num
  rw [hcast, Polynomial.Chebyshev.T_one, Polynomial.X_comp, bandMap_eval]
  norm_num

/-- **The composite on the fixture, theorem route** — the spectral
discharge fires end-to-end: the Krylov space `K₂(diag310, b)` contains
a nonzero vector within the delivered bound of the top eigenvalue. All
twelve hypotheses are discharged on literals, `hpar` through the
eigen-equation argument above. -/
theorem kanielPaigeChebyshev_diag310_QA :
    ∃ x ∈ krylovSpan diag310 bvec310 2, x ≠ 0 ∧
      (3 : ℝ) - rayleigh diag310 x ≤ (3 - 0) * (4/5) ^ 2 / (3/5) ^ 2 /
        (((Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).comp
          (bandMap (1:ℝ) 0)).eval 3) ^ 2 := by
  refine kanielPaigeChebyshev diag310 diag310_symm bvec310
    u310 g310 (3/5) (4/5) 3 1 0 2
    (by
      funext i
      fin_cases i <;>
        simp [bvec310, u310, g310, Pi.smul_apply, smul_eq_mul,
          Pi.add_apply])
    diag310_mulVec_u310_raw_QA
    (by simp [u310, Matrix.dotProduct, Fin.sum_univ_three])
    (by norm_num [u310, g310, Matrix.dotProduct, Fin.sum_univ_three])
    (by norm_num [g310, Matrix.dotProduct, Fin.sum_univ_three])
    (by norm_num)
    (by norm_num)
    (by norm_num)
    diag310_hpar_QA
    (by norm_num)

/-- The delivered bound's value on the same data pins to `16/75`
(compose `diag310_chebPoly_value_QA`): the instantiated statement is
numerically concrete. -/
theorem kanielPaigeChebyshev_diag310_value_QA :
    (3 - 0) * (4/5) ^ 2 / (3/5) ^ 2 /
        (((Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).comp
          (bandMap (1:ℝ) 0)).eval 3) ^ 2 = 16/75 := by
  rw [diag310_chebPoly_value_QA]
  norm_num

set_option linter.unnecessarySeqFocus false in
/-- **The raw route to the same mathematical content**, independent of
the discharge machinery: `xraw310` is the generator combination
`2 (M b) − b` (membership in `K₂` by the span's own definition, no
polynomial interface), it is nonzero, and its Rayleigh value is
`691/241` computed raw — so the true gap is `32/241 ≈ 0.133`,
comfortably inside the delivered `16/75 ≈ 0.213`. A wrong constant
anywhere in the discharge chain contradicts this hand computation. -/
theorem kanielPaigeChebyshev_diag310_raw_QA :
    xraw310 ∈ krylovSpan diag310 bvec310 2 ∧ xraw310 ≠ 0 ∧
      (3 : ℝ) - rayleigh diag310 xraw310 ≤ 16/75 := by
  have hMb : diag310 *ᵥ bvec310
      = fun j => if j = 0 then 9/5 else if j = 1 then 4/5 else 0 := by
    funext i
    fin_cases i <;>
      simp [diag310, bvec310, Matrix.diagonal_apply, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_three, Pi.smul_apply,
        smul_eq_mul] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · have hcombo : xraw310
        = (2 : ℝ) • (diag310 *ᵥ bvec310) + (-1 : ℝ) • bvec310 := by
      rw [hMb]
      funext i
      fin_cases i <;>
        simp [xraw310, bvec310, Pi.smul_apply, smul_eq_mul,
          Pi.add_apply] <;> norm_num
    rw [krylovSpan, hcombo]
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨1, by norm_num⟩, by
        simp [pow_one]⟩)
    · refine Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨0, by norm_num⟩, by
        simp [pow_zero, Matrix.one_mulVec]⟩)
  · intro h0
    have : xraw310 0 = (0 : Fin 3 → ℝ) 0 := congrFun h0 0
    norm_num [xraw310] at this
  · have hne : xraw310 ≠ 0 := by
      intro h0
      have : xraw310 0 = (0 : Fin 3 → ℝ) 0 := congrFun h0 0
      norm_num [xraw310] at this
    have hMx : diag310 *ᵥ xraw310
        = fun j => if j = 0 then 9 else if j = 1 then 4/5 else 0 := by
      funext i
      fin_cases i <;>
        simp [diag310, xraw310, Matrix.diagonal_apply, Matrix.mulVec,
          Matrix.dotProduct, Fin.sum_univ_three, Pi.smul_apply,
          smul_eq_mul] <;> norm_num
    rw [rayleigh, if_neg hne, quadForm]
    simp [diag310, xraw310, hMx, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three];
      norm_num

/-- **The unit decomposition instantiated**: on the same fixture data,
`b` decomposes as the theorem promises, with both content pins forced —
`c = 3/5` (orthogonality makes `c = u ⬝ᵥ b`) and `s² = 16/25` (the
norm makes `c² + s² = 1`) — so the existential is numerically pinned,
not vacuous. -/
theorem unit_decomposition_diag310_QA :
    ∃ (c s : ℝ) (g : Fin 3 → ℝ),
      bvec310 = c • u310 + s • g ∧ Matrix.dotProduct u310 g = 0 ∧
        Matrix.dotProduct g g ≤ 1 ∧ c ^ 2 + s ^ 2 = 1 ∧
        c = 3/5 ∧ s ^ 2 = 16/25 := by
  obtain ⟨c, s, g, h1, h2, h3, h4⟩ :=
    exists_unit_decomposition u310 bvec310
      (by simp [u310, Matrix.dotProduct, Fin.sum_univ_three])
      (by simp [bvec310, Matrix.dotProduct, Fin.sum_univ_three]; norm_num)
  have hraw : u310 ⬝ᵥ bvec310 = 3/5 := by
    simp [u310, bvec310, Matrix.dotProduct, Fin.sum_univ_three]
  have hdec : u310 ⬝ᵥ bvec310 = c := by
    rw [h1]
    simp only [Matrix.dotProduct_add, Matrix.dotProduct_smul,
      Matrix.smul_dotProduct, smul_eq_mul, h2]
    simp [u310, Matrix.dotProduct, Fin.sum_univ_three]
  have hc : c = 3/5 := hdec.symm.trans hraw
  refine ⟨c, s, g, h1, h2, h3, h4, hc, ?_⟩
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linear_combination h4
  rw [hs2, hc]
  norm_num

/-!
## Step 1c: the final statement — instantiation, degenerate case,
tightness, and the simple-top guard refuted
-/

/-- **The final statement instantiated on the `diag(3,1,0)` fixture**
at `k = 2`: no `c`/`s`/`g` hypotheses remain — the unit decomposition
is internal — and the only starting-vector hypothesis is
`u ⬝ᵥ b ≠ 0`, here discharged numerically (`3/5 ≠ 0`). -/
theorem kanielPaige_diag310_QA :
    ∃ x ∈ krylovSpan diag310 bvec310 2, x ≠ 0 ∧
      (3 : ℝ) - rayleigh diag310 x
        ≤ (3 - 0) * (1 - (u310 ⬝ᵥ bvec310) ^ 2) / (u310 ⬝ᵥ bvec310) ^ 2
          / (Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).eval
              (1 + 2 * (3 - 1) / (1 - 0)) ^ 2 :=
  kanielPaige diag310 diag310_symm u310 bvec310 3 1 0 2
    diag310_mulVec_u310_raw_QA
    (by simp [u310, Matrix.dotProduct, Fin.sum_univ_three])
    (by simp [bvec310, Matrix.dotProduct, Fin.sum_univ_three]; norm_num)
    (by simp [u310, bvec310, Matrix.dotProduct, Fin.sum_univ_three])
    (by norm_num) (by norm_num)
    diag310_hpar_QA
    (by norm_num)

/-- **The Chebyshev value, two routes to one number**: the final
statement's `γ`-form `T₁(1 + 2γ) = T₁(5)` computed raw (through
`T_one`, independent of the band map), and the 1b composite's composed
form `(T₁ ∘ w)(3)` — both are `5`, so the identification
`w(Ltop) = 1 + 2γ` holds numerically on the fixture. -/
theorem kanielPaige_final_chebValue_twoRoutes_QA :
    (Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).eval
        (1 + 2 * (3 - 1) / (1 - 0)) = 5 ∧
      ((Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).comp
        (bandMap (1:ℝ) 0)).eval 3 = 5 :=
  ⟨by
      have hcast : (((2 - 1 : ℕ) : ℤ)) = 1 := by norm_num
      rw [hcast, Polynomial.Chebyshev.T_one, Polynomial.eval_X]
      norm_num,
    diag310_chebPoly_value_QA⟩

/-- **The tan²φ restatement preserved the constant**: the final
statement's bound at the fixture data equals the 1b composite's bound
*as expressions*, `16/75` on both sides — a wrong `γ`-form or an
inverted `tan²φ` anywhere in the final statement's phrasing changes
the left-hand number and contradicts this equality. -/
theorem kanielPaige_final_bound_eq_composite_QA :
    (3 - 0) * (1 - (u310 ⬝ᵥ bvec310) ^ 2) / (u310 ⬝ᵥ bvec310) ^ 2
        / (Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).eval
            (1 + 2 * (3 - 1) / (1 - 0)) ^ 2
      = (3 - 0) * (4/5) ^ 2 / (3/5) ^ 2
          / (((Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).comp
              (bandMap (1:ℝ) 0)).eval 3) ^ 2 := by
  have hdot : u310 ⬝ᵥ bvec310 = 3/5 := by
    simp [u310, bvec310, Matrix.dotProduct, Fin.sum_univ_three]
  rw [hdot, kanielPaige_final_chebValue_twoRoutes_QA.1,
    kanielPaige_final_chebValue_twoRoutes_QA.2]
  norm_num

/-- **The final bound's value and the true gap strictly inside**:
composed with the two lemmas above and 1b's composite value, the final
bound pins to `16/75`, and the raw-route true gap `32/241` (1b's
`kanielPaigeChebyshev_diag310_raw_QA` exhibited the witness whose
Rayleigh value is `691/241`) is *strictly* inside it. -/
theorem kanielPaige_diag310_final_value_QA :
    (u310 ⬝ᵥ bvec310) = 3/5 ∧
      (3 - 0) * (1 - (u310 ⬝ᵥ bvec310) ^ 2) / (u310 ⬝ᵥ bvec310) ^ 2
        / (Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).eval
            (1 + 2 * (3 - 1) / (1 - 0)) ^ 2 = 16/75 ∧
      (32 : ℝ)/241 < 16/75 := by
  have hdot : u310 ⬝ᵥ bvec310 = 3/5 := by
    simp [u310, bvec310, Matrix.dotProduct, Fin.sum_univ_three]
  refine ⟨hdot, ?_, by norm_num⟩
  rw [kanielPaige_final_bound_eq_composite_QA,
    kanielPaigeChebyshev_diag310_value_QA]

/-- **The degenerate Chebyshev factor at `k = 1`**: `T₀ ≡ 1` at any
argument — the Chebyshev acceleration contributes nothing, so the
`k = 1` bound must reduce to the plain one-step Rayleigh-gap
statement. -/
theorem cheb_T0_degenerate_QA :
    (Polynomial.Chebyshev.T ℝ ((1 - 1 : ℕ) : ℤ)).eval
      (1 + 2 * (3 - 1) / (1 - 0)) = 1 := by
  have hcast : (((1 - 1 : ℕ) : ℤ)) = 0 := by norm_num
  rw [hcast, Polynomial.Chebyshev.T_zero, Polynomial.eval_one]

/-- **The final statement at `k = 1`** — every hypothesis discharged on
the same fixture data; the Krylov space is the line `ℝ · b`, so the
bound is the plain Rayleigh-gap statement for `b` itself. -/
theorem kanielPaige_diag310_k1_QA :
    ∃ x ∈ krylovSpan diag310 bvec310 1, x ≠ 0 ∧
      (3 : ℝ) - rayleigh diag310 x
        ≤ (3 - 0) * (1 - (u310 ⬝ᵥ bvec310) ^ 2) / (u310 ⬝ᵥ bvec310) ^ 2
          / (Polynomial.Chebyshev.T ℝ ((1 - 1 : ℕ) : ℤ)).eval
              (1 + 2 * (3 - 1) / (1 - 0)) ^ 2 :=
  kanielPaige diag310 diag310_symm u310 bvec310 3 1 0 1
    diag310_mulVec_u310_raw_QA
    (by simp [u310, Matrix.dotProduct, Fin.sum_univ_three])
    (by simp [bvec310, Matrix.dotProduct, Fin.sum_univ_three]; norm_num)
    (by simp [u310, bvec310, Matrix.dotProduct, Fin.sum_univ_three])
    (by norm_num) (by norm_num)
    diag310_hpar_QA
    (by norm_num)

/-- The starting vector's Rayleigh value computed raw from the
definitions (`M b = (9/5, 4/5, 0)`, `b ⬝ᵥ M b = 43/25`, `b ⬝ᵥ b = 1`) —
independent of every theorem — so the `k = 1` gap `3 − 43/25 = 32/25`
is a hand-checked number. -/
theorem rayleigh_diag310_bvec310_raw_QA :
    rayleigh diag310 bvec310 = 43/25 := by
  have hne : bvec310 ≠ 0 := by
    intro h0
    have h : bvec310 0 = (0 : Fin 3 → ℝ) 0 := congrFun h0 0
    simp [bvec310] at h
  have hMb : diag310 *ᵥ bvec310
      = fun j => if j = 0 then 9/5 else if j = 1 then 4/5 else 0 := by
    funext i
    fin_cases i <;>
      simp [diag310, bvec310, Matrix.diagonal_apply, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_three, Pi.smul_apply,
        smul_eq_mul]; norm_num
  rw [rayleigh, if_neg hne, quadForm, hMb]
  simp [bvec310, Matrix.dotProduct, Fin.sum_univ_three]; norm_num

/-- **The `k = 1` degenerate case recovers the plain Rayleigh gap**:
the bound evaluates to the Chebyshev-free value
`(Ltop − Lbot) · tan²φ = 3 · 16/9 = 16/3` (through `T₀ ≡ 1`), and the
actual gap at the only Krylov direction — `3 − R(b) = 3 − 43/25 =
32/25`, raw — sits inside it. -/
theorem kanielPaige_diag310_k1_value_QA :
    (3 : ℝ) - 43/25 = 32/25 ∧
      (3 - 0) * (1 - (u310 ⬝ᵥ bvec310) ^ 2) / (u310 ⬝ᵥ bvec310) ^ 2
        / (Polynomial.Chebyshev.T ℝ ((1 - 1 : ℕ) : ℤ)).eval
            (1 + 2 * (3 - 1) / (1 - 0)) ^ 2 = 16/3 ∧
      32/25 ≤ 16/3 := by
  have hdot : u310 ⬝ᵥ bvec310 = 3/5 := by
    simp [u310, bvec310, Matrix.dotProduct, Fin.sum_univ_three]
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [hdot, cheb_T0_degenerate_QA]
  norm_num

/-- The fixture's top-eigenvalue Rayleigh ceiling, raw: `R(y) ≤ 3` for
every nonzero `y` (`3y₀² + y₁² ≤ 3(y₀² + y₁² + y₂²)`), used by the
tightness witness to pin the delivered witness's Rayleigh value from
above independently of the theorem. -/
theorem rayleigh_diag310_le_three_QA {y : Fin 3 → ℝ} (hy : y ≠ 0) :
    rayleigh diag310 y ≤ 3 := by
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ y j * y j :=
    fun j _ => mul_self_nonneg _
  have hsum : (0:ℝ) ≤ y ⬝ᵥ y := Finset.sum_nonneg hnn
  have hd0 : (0:ℝ) < y ⬝ᵥ y := by
    rcases eq_or_lt_of_le hsum with h | h
    · exfalso
      have hyz : ∀ j ∈ (Finset.univ : Finset (Fin 3)), y j * y j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h.symm
      exact hy (funext fun j => by
        simpa using mul_self_eq_zero.1 (hyz j (Finset.mem_univ j)))
    · exact h
  have hq : y ⬝ᵥ (diag310 *ᵥ y) = 3 * (y 0) ^ 2 + (y 1) ^ 2 := by
    simp [diag310, Matrix.mulVec, Matrix.dotProduct,
      Matrix.diagonal_apply, Fin.sum_univ_three]
    ring
  have hd' : y ⬝ᵥ y = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_three]
    ring
  rw [rayleigh, if_neg hy, quadForm, hq, div_le_iff₀ hd0, hd']
  nlinarith [sq_nonneg (y 1), sq_nonneg (y 2)]

/-- **The `b = u` tightness witness**: at `tan φ = 0` the bound is
exactly `0`, and the delivered witness *attains* it — its Rayleigh
value is pinned to exactly `Ltop = 3` from both sides (the theorem
gives `3 − R(x) ≤ 0`; the raw ceiling gives `R(x) ≤ 3`). A looser
final-form phrasing — a nonzero bound at `c = 1`, or a witness short
of the top — contradicts this pair. -/
theorem kanielPaige_tightness_bEqU_QA :
    ((3 - 0) * (1 - (u310 ⬝ᵥ u310) ^ 2) / (u310 ⬝ᵥ u310) ^ 2
        / (Polynomial.Chebyshev.T ℝ ((2 - 1 : ℕ) : ℤ)).eval
          (1 + 2 * (3 - 1) / (1 - 0)) ^ 2) = 0 ∧
      ∃ x ∈ krylovSpan diag310 u310 2, x ≠ 0 ∧ rayleigh diag310 x = 3 := by
  have hd : u310 ⬝ᵥ u310 = 1 := by
    simp [u310, Matrix.dotProduct, Fin.sum_univ_three]
  obtain ⟨x, hxmem, hx0, hxb⟩ :=
    kanielPaige diag310 diag310_symm u310 u310 3 1 0 2
      diag310_mulVec_u310_raw_QA
      (by simp [u310, Matrix.dotProduct, Fin.sum_univ_three])
      (by simp [u310, Matrix.dotProduct, Fin.sum_univ_three])
      (by simp [u310, Matrix.dotProduct, Fin.sum_univ_three])
      (by norm_num) (by norm_num)
      diag310_hpar_QA
      (by norm_num)
  refine ⟨?_, x, hxmem, hx0, ?_⟩
  · rw [kanielPaige_final_chebValue_twoRoutes_QA.1]
    norm_num [hd]
  · have hle := rayleigh_diag310_le_three_QA hx0
    rw [kanielPaige_final_chebValue_twoRoutes_QA.1, hd] at hxb
    norm_num at hxb
    linarith

/-! ### The simple-top guard refuted on a top-multiplicity fixture

`diag(3, 3, 0)` has `λ₁ = λ₂ = 3`: the top eigenvalue is *not* simple.
Every hypothesis of `kanielPaige` except `hpar` holds on this data
(symmetry, `u = e₁` a unit eigenvector at `Ltop = 3`, `b = (2/3, 2/3,
1/3)` unit with `u ⬝ᵥ b = 2/3 ≠ 0`, `14/5 < 29/10 ≤ 3`, `k = 1`), the
band `[14/5, 29/10]` contains neither `3` nor `0`, and the conclusion
is *false* there — so `hpar` (the simple-top guard) is load-bearing.
-/

/-- The top-multiplicity fixture `diag(3, 3, 0)`: `λ₁ = λ₂ = 3`. -/
def diag330 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun j => if j = 0 then 3 else if j = 1 then 3 else 0

/-- The top-eigenvalue direction `e₁`, entrywise (also the eigenvector
the refuted `hpar` would force everything to be a multiple of). -/
def u330 : Fin 3 → ℝ := fun j => if j = 0 then 1 else 0

/-- The starting vector `b = (2/3, 2/3, 1/3)`: unit, all coordinates
nonzero (`4/9 + 4/9 + 1/9 = 1`). -/
noncomputable def bvec330 : Fin 3 → ℝ :=
  fun j => if j = 0 then 2/3 else if j = 1 then 2/3 else 1/3

theorem diag330_symm_QA : diag330.IsSymm := by
  show diag330ᵀ = diag330
  exact Matrix.diagonal_transpose _

theorem diag330_mulVec_u330_raw_QA :
    diag330 *ᵥ u330 = (3 : ℝ) • u330 := by
  funext i
  fin_cases i <;>
    simp [diag330, u330, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]

/-- Every eigenvalue of `diag330` is `3` or `0` — derived from the
eigen-equation alone (a `μ` off both values forces every coordinate of
the eigenvector to vanish, against the unit norm). -/
theorem diag330_eigval_two_vals_QA (i : Fin 3) :
    eigvalOf diag330 diag330_symm i = 3 ∨
      eigvalOf diag330 diag330_symm i = 0 := by
  set μ : ℝ := eigvalOf diag330 diag330_symm i with hμ
  set v : Fin 3 → ℝ := eigvecOf diag330 diag330_symm i with hv
  have hev : diag330 *ᵥ v = μ • v :=
    (isHermitian_of_isSymm diag330_symm).mulVec_eigenvectorBasis i
  have hvv : v ⬝ᵥ v = 1 := by
    have h := eigvecOf_inner diag330 diag330_symm i i
    rw [← hv] at h
    simpa [Matrix.dotProduct] using h
  by_contra hne
  have hμ3 : μ ≠ 3 := fun h => hne (Or.inl h)
  have hμ0 : μ ≠ 0 := fun h => hne (Or.inr h)
  have hc0 : (3 : ℝ) * v 0 = μ * v 0 := by
    simpa [diag330, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] using congrFun hev 0
  have hc1 : (3 : ℝ) * v 1 = μ * v 1 := by
    simpa [diag330, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] using congrFun hev 1
  have hc2 : (0 : ℝ) = μ * v 2 := by
    simpa [diag330, Matrix.diagonal_apply, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] using congrFun hev 2
  have hv0 : v 0 = 0 := by
    have hkey : v 0 * (3 - μ) = 0 := by linear_combination hc0
    rcases mul_eq_zero.1 hkey with h | h
    · exact h
    · exact absurd (by linarith : μ = 3) hμ3
  have hv1 : v 1 = 0 := by
    have hkey : v 1 * (3 - μ) = 0 := by linear_combination hc1
    rcases mul_eq_zero.1 hkey with h | h
    · exact h
    · exact absurd (by linarith : μ = 3) hμ3
  have hv2 : v 2 = 0 := by
    rcases mul_eq_zero.1 hc2.symm with h | h
    · exact absurd h hμ0
    · exact h
  have hvz : v = 0 := by
    funext j
    fin_cases j <;> simp [hv0, hv1, hv2]
  rw [hvz] at hvv
  simp at hvv

/-- **The guard hypothesis itself is false on this fixture**: no valid
`hpar` exists at the band `[14/5, 29/10]` — the band contains neither
eigenvalue, so `hpar` would make all three orthonormal
`eigvecOf` directions multiples of `e₁`, and two orthogonal unit
vectors cannot both lie in one line (`t₀t₁ = 0` against
`t₀² = t₁² = 1`). This is exactly the `λ₁ = λ₂` obstruction the guard
excludes. -/
theorem kanielPaige_topGuard_hpar_fails_QA :
    ¬ (∀ i : Fin 3, ¬(14/5 ≤ eigvalOf diag330 diag330_symm i ∧
        eigvalOf diag330 diag330_symm i ≤ 29/10) →
      ∃ t : ℝ, eigvecOf diag330 diag330_symm i = t • u330) := by
  intro hpar
  have hout : ∀ i : Fin 3,
      ¬(14/5 ≤ eigvalOf diag330 diag330_symm i ∧
        eigvalOf diag330 diag330_symm i ≤ 29/10) := by
    intro i hi
    rcases diag330_eigval_two_vals_QA i with h | h
    · rw [h] at hi
      norm_num at hi
    · rw [h] at hi
      norm_num at hi
  obtain ⟨t0, ht0⟩ := hpar 0 (hout 0)
  obtain ⟨t1, ht1⟩ := hpar 1 (hout 1)
  have huu : u330 ⬝ᵥ u330 = 1 := by
    simp [u330, Matrix.dotProduct, Fin.sum_univ_three]
  have h01 : (eigvecOf diag330 diag330_symm 0)
      ⬝ᵥ (eigvecOf diag330 diag330_symm 1) = 0 := by
    have h := eigvecOf_inner diag330 diag330_symm 0 1
    simpa [Matrix.dotProduct] using h
  have h00 : (eigvecOf diag330 diag330_symm 0)
      ⬝ᵥ (eigvecOf diag330 diag330_symm 0) = 1 := by
    have h := eigvecOf_inner diag330 diag330_symm 0 0
    simpa [Matrix.dotProduct] using h
  have h11 : (eigvecOf diag330 diag330_symm 1)
      ⬝ᵥ (eigvecOf diag330 diag330_symm 1) = 1 := by
    have h := eigvecOf_inner diag330 diag330_symm 1 1
    simpa [Matrix.dotProduct] using h
  rw [ht0, ht1, Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_smul,
    smul_eq_mul, huu, mul_one] at h01
  rw [ht0, Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_smul,
    smul_eq_mul, huu, mul_one] at h00
  rw [ht1, Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_smul,
    smul_eq_mul, huu, mul_one] at h11
  -- h00 : t0 * t0 = 1, h11 : t1 * t1 = 1, h01 : t0 * t1 = 0 — impossible
  have hprod : (t0 * t1) ^ 2 = 1 := by
    nlinarith [h00, h11]
  rw [h01] at hprod
  norm_num at hprod

/-- **The hypothesis-free form of the final statement is false**: with
every hypothesis except `hpar` verified on the fixture (`u = e₁` a unit
top eigenvector, `b` unit with `u ⬝ᵥ b = 2/3 ≠ 0`, `14/5 < 29/10 ≤ 3`,
`k = 1`) the *conclusion itself is refuted* — the `k = 1` Krylov space
is the line `ℝ · b` (the span-collapse argument), every nonzero vector
on it has Rayleigh value exactly `8/3` (computed raw, by linearity from
`b ⬝ᵥ b = 1` and `b ⬝ᵥ Mb = 8/3`), so the actual gap is `1/3`, while
the bound evaluates to `1/4` (`(3 − 14/5) · tan²φ / T₀(3)² =
(1/5)(5/4)/1`). The simple-top guard is load-bearing, not decoration. -/
theorem kanielPaige_topGuard_refuted_QA :
    ¬ (∃ x ∈ krylovSpan diag330 bvec330 1, x ≠ 0 ∧
        (3 : ℝ) - rayleigh diag330 x
          ≤ (3 - 14/5) * (1 - (u330 ⬝ᵥ bvec330) ^ 2)
              / (u330 ⬝ᵥ bvec330) ^ 2
            / (Polynomial.Chebyshev.T ℝ ((1 - 1 : ℕ) : ℤ)).eval
                (1 + 2 * (3 - 29/10) / (29/10 - 14/5)) ^ 2) := by
  rintro ⟨x, hxmem, hx0, hxb⟩
  -- the Krylov span at k = 1 is the line ℝ • b
  have hrange : Set.range (fun i : Fin 1 =>
      (diag330 ^ (i : ℕ)) *ᵥ bvec330) = {bvec330} := by
    ext z
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      simp only [pow_zero, Matrix.one_mulVec] at hi
      exact hi.symm
    · rintro rfl
      exact ⟨0, by simp [pow_zero, Matrix.one_mulVec]⟩
  rw [krylovSpan, hrange, Submodule.mem_span_singleton] at hxmem
  obtain ⟨r, hr⟩ := hxmem
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hr
    exact hx0 hr.symm
  have hrr0 : (r : ℝ) * r ≠ 0 := mul_ne_zero hr0 hr0
  -- the raw fixture facts
  have hbb : bvec330 ⬝ᵥ bvec330 = 1 := by
    simp [bvec330, Matrix.dotProduct, Fin.sum_univ_three]; norm_num
  have hMb : diag330 *ᵥ bvec330
      = fun j => if j = 0 then 2 else if j = 1 then 2 else 0 := by
    funext i
    fin_cases i <;>
      simp [diag330, bvec330, Matrix.diagonal_apply, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_three] <;> norm_num
  have hq : bvec330 ⬝ᵥ (diag330 *ᵥ bvec330) = 8/3 := by
    rw [hMb]
    simp [bvec330, Matrix.dotProduct, Fin.sum_univ_three]; norm_num
  have hub : u330 ⬝ᵥ bvec330 = 2/3 := by
    simp [u330, bvec330, Matrix.dotProduct, Fin.sum_univ_three]
  have hT0 : (Polynomial.Chebyshev.T ℝ ((1 - 1 : ℕ) : ℤ)).eval
      (1 + 2 * (3 - 29/10) / (29/10 - 14/5)) = 1 := by
    have hcast : (((1 - 1 : ℕ) : ℤ)) = 0 := by norm_num
    rw [hcast, Polynomial.Chebyshev.T_zero, Polynomial.eval_one]
  -- the Rayleigh value of x = r • b, by linearity
  have hdd : x ⬝ᵥ x = r * r * (bvec330 ⬝ᵥ bvec330) := by
    rw [← hr, Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_smul,
      smul_eq_mul]
  have hqq : x ⬝ᵥ (diag330 *ᵥ x)
      = r * r * (bvec330 ⬝ᵥ (diag330 *ᵥ bvec330)) := by
    rw [← hr, Matrix.smul_dotProduct, Matrix.mulVec_smul,
      Matrix.dotProduct_smul, smul_smul, smul_eq_mul]
  have hquot : (r : ℝ) * r * (8/3) / (r * r) = 8/3 := by
    rw [div_eq_iff hrr0]
    ring
  rw [rayleigh, if_neg hx0, quadForm, hqq, hdd, hbb, mul_one, hq,
    hquot] at hxb
  rw [hub, hT0] at hxb
  norm_num at hxb

end SpectralGraphTheory.QA
