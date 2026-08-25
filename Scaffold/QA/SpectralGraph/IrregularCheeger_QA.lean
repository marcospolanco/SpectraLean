/-
  IrregularCheeger_QA.lean

  Purpose
  -------
  QA for the irregular Cheeger upper bound delivered in
  `Scaffold.Mathlib.GraphTheory.VariationalTransfer` (proposal
  `proposals/irregular-cheeger-variational-transfer.md`, 2026-08-25):
  `cheeger_upper_bound_normalized` — `secondEval (normalizedLaplacian A)
  ≤ 2 * cheegerConstant A` on arbitrary symmetric nonnegative
  positive-degree graphs — together with its engine, the general-kernel
  variational lemma `secondEval_le_rayleigh_of_ker`
  (`Scaffold.Mathlib.GraphTheory.Spectral`), and its degree-stretched
  cut-test-vector layer.

  Sections:

  - **The genuinely-irregular fixture `P₃`** (`icPathAdj`, degrees
    `1, 2, 1` — no `d`-regularity anywhere): the conductance side
    computed by hand (`cheegerConstant = 1`, every cut's conductance
    `1`), the test-vector layer verified entrywise (the stretched cut
    indicator `![3, -√2, -1]`, its kernel orthogonality both by the new
    theorem and by raw arithmetic, its norm `12 = vol S · vol Sᶜ · vol V`,
    its energy `16` by three independent routes: raw combinatorial
    arithmetic, the congruence engine, and the delivered cut energy
    identity), and the spectral side bounded **independently of the
    theorem** through the eigenpair witness `![1, 0, -1]` at eigenvalue
    `1` — a route through the new general-kernel lemma.

  - **The discrimination witness**: the stretched cut test vector is
    *not* orthogonal to `onesVec` (`2 - √2 ≠ 0`), which is exactly why
    the delivered `secondEval_le_rayleigh` (onesVec-orthogonality)
    cannot express the irregular route and the general-kernel form was
    needed.

  - **Regular recovery on `K₂`** (`edgeAdj`, reused from `Cheeger_QA` by
    QA-to-QA import): the new theorem's spectral side equals the regular
    family's (`normalizedLaplacian = regularNormalizedLaplacian` on the
    cone), and the instantiation reads `2 ≤ 2 · 1` — the tight
    recovery the regular QA pinned, now reached through the irregular
    route.

  - **The PSD fence on the general-kernel engine**: `diag(-1, 0)` with
    kernel vector `e₁` and test vector `e₀` — every hypothesis except
    PSD holds (verified), the conclusion `0 ≤ -1` is false (the sorted
    spectrum `[-1, 0]` and Rayleigh quotient `-1` both computed), so
    `hpsd` is isolated.

  - **The degree fence on the headline**: the all-zero adjacency on
    `Fin 2` — symmetric, nonnegative, `2 ≤ card`, but every degree is
    `0` so `hd` fails; the conductance is junk-zero (`0/0`) while
    `λ₂ (normalizedLaplacian 0) = λ₂ (1) = 1`, refuting the
    hypothesis-free conclusion `1 ≤ 0`.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove any axiom; it checks that the interfaces compose on
  genuinely irregular input.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.QA.SpectralGraph.Cheeger_QA

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Shared helper: `secondEval` is independent of the symmetry proof
-/

/-- `secondEval` does not depend on which symmetry proof it carries
(Prop-valued argument), only on the matrix — used to transport the
K₂ spectral pin across the cone agreement
`normalizedLaplacian = regularNormalizedLaplacian`. -/
private theorem secondEval_congr {V₂ : Type} [Fintype V₂] [DecidableEq V₂]
    {M₁ M₂ : Matrix V₂ V₂ ℝ} (hM₁ : M₁.IsSymm) (hM₂ : M₂.IsSymm)
    (hcard : 2 ≤ Fintype.card V₂) (h : M₁ = M₂) :
    secondEval M₁ hM₁ hcard = secondEval M₂ hM₂ hcard := by
  subst h
  rfl

/-!
## The irregular fixture: the path P₃ (degrees 1, 2, 1)
-/

/-- The adjacency of the three-vertex path `0 — 1 — 2`: genuinely
irregular (degrees `1, 2, 1`), symmetric, nonnegative. -/
def icPathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem icPathAdj_symmetric : icPathAdj.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [icPathAdj]

theorem icPathAdj_nonneg : ∀ i j, 0 ≤ icPathAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [icPathAdj]

theorem icPathAdj_deg : ∀ i, deg icPathAdj i = if i = 1 then 2 else 1 := by
  intro i
  fin_cases i
  all_goals simp [deg, icPathAdj, Fin.sum_univ_three]
  all_goals norm_num

theorem icPathAdj_pos_deg : ∀ i, 0 < deg icPathAdj i := by
  intro i
  fin_cases i <;> simp [icPathAdj_deg]

/-- Total volume `4` and the two cut volumes of `S = {0}`. -/
theorem icPathAdj_vol_univ :
    vol icPathAdj (Finset.univ : Finset (Fin 3)) = 4 := by
  simp [vol, icPathAdj_deg, Fin.sum_univ_three]
  norm_num

theorem icPathAdj_vol_zero :
    vol icPathAdj ({0} : Finset (Fin 3)) = 1 := by
  simp [vol, icPathAdj_deg]

theorem icPathAdj_vol_zero_compl :
    vol icPathAdj ({0} : Finset (Fin 3))ᶜ = 3 := by
  have : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
  rw [this]
  simp [vol, icPathAdj_deg]
  norm_num

theorem icPathAdj_boundary_zero :
    boundary icPathAdj ({0} : Finset (Fin 3)) = 1 := by
  have hcompl : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
  rw [boundary, hcompl]
  simp [icPathAdj]

/-- The cut test vector at `S = {0}`: `vol Sᶜ = 3` on `S`, `-vol S = -1`
off it. -/
theorem icPathAdj_cutVec :
    cutTestVector icPathAdj ({0} : Finset (Fin 3)) = ![3, -1, -1] := by
  funext i
  fin_cases i <;>
    simp [cutTestVector_apply, icPathAdj_vol_zero, icPathAdj_vol_zero_compl]

/-- The degree-stretched cut test vector: `√D · x` at `√D = diag(1, √2,
1)` — the irregular test object. -/
theorem icPathAdj_stretchVec :
    degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3))
      = ![3, -Real.sqrt 2, -1] := by
  funext i
  fin_cases i <;>
    simp [degreeSqrt_mulVec, icPathAdj_cutVec, icPathAdj_deg,
      Matrix.mulVec_diagonal, Real.sqrt_one]

/-- The normalized Laplacian's kernel vector on `P₃`: `√D · 1 = ![1, √2,
1]` — *not* a constant vector (the structural fact separating the
irregular variational picture). -/
theorem icPathAdj_kernelVec :
    degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ) = ![1, Real.sqrt 2, 1] := by
  funext i
  fin_cases i <;>
    simp [degreeSqrt_mulVec, icPathAdj_deg, Matrix.mulVec_diagonal,
      Real.sqrt_one, onesVec]

theorem icPathAdj_sqrt_two_sq :
    (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := by
  rw [Real.mul_self_sqrt]
  norm_num

/-- **Kernel orthogonality by raw arithmetic**: the stretched cut test
vector is orthogonal to `√D · 1` on genuinely irregular input —
`3 · 1 + (-√2) · √2 + (-1) · 1 = 3 - 2 - 1 = 0`. -/
theorem icPathAdj_ortho_raw :
    Matrix.dotProduct
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
        (degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ)) = 0 := by
  simp only [Matrix.dotProduct, icPathAdj_stretchVec, icPathAdj_kernelVec,
    Fin.sum_univ_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    icPathAdj_sqrt_two_sq]

/-- **The discrimination witness**: the stretched cut test vector is
*not* orthogonal to `onesVec` (`2 - √2 ≠ 0`) — the delivered
onesVec-based `secondEval_le_rayleigh` provably cannot consume this test
object; the general-kernel form is genuinely more expressive, not a
restatement. -/
theorem icPathAdj_not_ortho_onesVec :
    Matrix.dotProduct
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
        (onesVec : Fin 3 → ℝ) ≠ 0 := by
  have hval :
      Matrix.dotProduct
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
        (onesVec : Fin 3 → ℝ)
        = 2 - Real.sqrt 2 := by
    simp only [Matrix.dotProduct, icPathAdj_stretchVec, onesVec, mul_one,
      Fin.sum_univ_three]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  rw [hval, sub_ne_zero]
  intro h
  nlinarith [icPathAdj_sqrt_two_sq, Real.sqrt_nonneg 2, h]

/-- The stretched cut test vector's norm: `9 + 2 + 1 = 12`, agreeing
with the theorem's `vol S · vol Sᶜ · vol V = 1 · 3 · 4`. -/
theorem icPathAdj_stretch_norm_raw :
    Matrix.dotProduct
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
      = 12 := by
  simp only [Matrix.dotProduct, icPathAdj_stretchVec, Fin.sum_univ_three]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    icPathAdj_sqrt_two_sq]

theorem icPathAdj_stretch_norm_thm :
    Matrix.dotProduct
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
      = vol icPathAdj ({0} : Finset (Fin 3))
          * vol icPathAdj ({0} : Finset (Fin 3))ᶜ
          * vol icPathAdj (Finset.univ : Finset (Fin 3)) :=
  dotProduct_degreeSqrt_mulVec_cutTestVector_self icPathAdj
    (fun i => le_of_lt (icPathAdj_pos_deg i)) _

/-- The two norm routes agree: theorem value `1 · 3 · 4 = 12` matches
the raw arithmetic. -/
theorem icPathAdj_stretch_norm_agree :
    vol icPathAdj ({0} : Finset (Fin 3))
        * vol icPathAdj ({0} : Finset (Fin 3))ᶜ
        * vol icPathAdj (Finset.univ : Finset (Fin 3)) = 12 := by
  rw [← icPathAdj_stretch_norm_thm, icPathAdj_stretch_norm_raw]

/-- **The combinatorial energy by raw arithmetic** (all integers): the
Laplacian `diag(1,2,1) - path` applied to `![3,-1,-1]` gives
`![4,-4,0]`, and the inner product is `3·4 + 1·4 + 0 = 16`. -/
theorem icPathAdj_comb_energy_raw :
    quadForm (laplacian icPathAdj)
        (cutTestVector icPathAdj ({0} : Finset (Fin 3))) = 16 := by
  have hVe : (laplacian icPathAdj) *ᵥ (![3, -1, -1] : Fin 3 → ℝ)
      = ![4, -4, 0] := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, laplacian, Matrix.sub_apply,
        degreeMatrix, deg, Fin.sum_univ_three, icPathAdj] <;>
      norm_num
  rw [quadForm, icPathAdj_cutVec, hVe]
  simp [Matrix.dotProduct, Fin.sum_univ_three]
  norm_num

/-- **Three independent energy routes agree at `16`**: raw combinatorial
arithmetic (`icPathAdj_comb_energy_raw`), the congruence engine
(`quadForm_laplacian_eq_quadForm_normalizedLaplacian` — the
`VariationalTransfer` module's own bridge), and the delivered cut energy
identity `quadForm_laplacian_cutTestVector` at `boundary = 1`,
`vol V = 4`. A mis-stated congruence or a wrong stretched vector breaks
exactly one of these. -/
theorem icPathAdj_norm_energy :
    quadForm (normalizedLaplacian icPathAdj)
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
      = 16 := by
  rw [← quadForm_laplacian_eq_quadForm_normalizedLaplacian icPathAdj
    icPathAdj_pos_deg _, icPathAdj_comb_energy_raw]

theorem icPathAdj_delivered_energy :
    quadForm (laplacian icPathAdj)
        (cutTestVector icPathAdj ({0} : Finset (Fin 3)))
      = boundary icPathAdj ({0} : Finset (Fin 3))
          * (vol icPathAdj (Finset.univ : Finset (Fin 3))) ^ 2 :=
  quadForm_laplacian_cutTestVector icPathAdj icPathAdj_symmetric _

theorem icPathAdj_energy_routes_agree :
    boundary icPathAdj ({0} : Finset (Fin 3))
          * (vol icPathAdj (Finset.univ : Finset (Fin 3))) ^ 2 = 16 := by
  rw [← icPathAdj_delivered_energy, icPathAdj_comb_energy_raw]

/-- The Rayleigh quotient of the stretched cut test vector:
`boundary · vol V / (vol S · vol Sᶜ) = 1 · 4 / (1 · 3) = 4/3`,
cross-checked against the raw pins `16 / 12`. -/
theorem icPathAdj_rayleigh :
    rayleigh (normalizedLaplacian icPathAdj)
        (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
      = 4 / 3 := by
  rw [rayleigh_normalizedLaplacian_degreeSqrt_cutTestVector icPathAdj
    icPathAdj_symmetric icPathAdj_pos_deg (by decide) (by decide),
    icPathAdj_boundary_zero, icPathAdj_vol_zero, icPathAdj_vol_zero_compl,
    icPathAdj_vol_univ]
  norm_num

/-!
### The spectral side independently: the eigenpair witness
-/

/-- The middle mode of the path: `![1, 0, -1]` is an eigenvector of the
normalized Laplacian of `P₃` at eigenvalue `1` (the true `λ₂`; the
spectrum is `{0, 1, 2}`). -/
def icEigVec : Fin 3 → ℝ := ![1, 0, -1]

/-- The eigen-equation, verified entrywise from the definition of
`normalizedLaplacian` (the `1/√2 · √2` cross terms cancelling in the
middle row). -/
theorem icPathAdj_normLap_mulVec_eigVec :
    normalizedLaplacian icPathAdj *ᵥ icEigVec = icEigVec := by
  have hentry : ∀ i j : Fin 3,
      normalizedLaplacian icPathAdj i j
        = (if i = j then (1 : ℝ) else 0)
          - (Real.sqrt (deg icPathAdj i))⁻¹ * icPathAdj i j
            * (Real.sqrt (deg icPathAdj j))⁻¹ := by
    intro i j
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
      Matrix.diagonal_apply]
  have hdeglit : ∀ i : Fin 3,
      deg !![0, 1, 0; 1, 0, 1; 0, 1, 0] i = if i = 1 then 2 else 1 := by
    intro i
    fin_cases i <;> simp [deg, Fin.sum_univ_three]
    all_goals norm_num
  funext i
  fin_cases i <;>
    simp only [hentry, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_three, icEigVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  all_goals
    simp [icPathAdj_deg, hdeglit, icPathAdj, Real.sqrt_one]

theorem icEigVec_ne_zero : icEigVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [icEigVec] at h0

theorem icEigVec_dot_self :
    Matrix.dotProduct icEigVec icEigVec = 2 := by
  simp only [Matrix.dotProduct, icEigVec, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

theorem icEigVec_ortho_kernel :
    Matrix.dotProduct icEigVec
        (degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ)) = 0 := by
  simp only [Matrix.dotProduct, icEigVec, icPathAdj_kernelVec,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  norm_num

/-- The kernel vector is nonzero on `P₃` (its middle entry is `√2`). -/
theorem icPathAdj_kernelVec_ne :
    degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [icPathAdj_kernelVec, Matrix.cons_val_one, Matrix.head_cons,
    Pi.zero_apply] at h1
  exact (Real.sqrt_ne_zero'.mpr (by norm_num)) h1

/-- **The independent spectral bound: `λ₂ (L_sym P₃) ≤ 1`**, through the
new general-kernel variational lemma at the eigenpair witness — computed
without the Cheeger theorem, so the theorem's own instantiation (`≤ 2`)
is cross-checked rather than circular. -/
theorem icPathAdj_secondEval_le_one :
    secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 3)) ≤ 1 := by
  have hquad : quadForm (normalizedLaplacian icPathAdj) icEigVec
      = Matrix.dotProduct icEigVec icEigVec := by
    rw [quadForm, icPathAdj_normLap_mulVec_eigVec]
  have hray : rayleigh (normalizedLaplacian icPathAdj) icEigVec = 1 := by
    rw [rayleigh, if_neg icEigVec_ne_zero, hquad, icEigVec_dot_self]
    try norm_num
  calc secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 3))
      ≤ rayleigh (normalizedLaplacian icPathAdj) icEigVec :=
          secondEval_le_rayleigh_of_ker
            (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
            (normalizedLaplacian_psd icPathAdj icPathAdj_symmetric
              icPathAdj_nonneg icPathAdj_pos_deg)
            icPathAdj_kernelVec_ne
            (normalizedLaplacian_mulVec_degreeSqrt_onesVec icPathAdj
              icPathAdj_pos_deg)
            (by decide) icEigVec_ne_zero icEigVec_ortho_kernel
    _ = 1 := hray

/-- **The same bound through the theorem's own test vector** — the
general-kernel lemma at the stretched cut indicator (a vector *not*
orthogonal to `onesVec`, per `icPathAdj_not_ortho_onesVec`), landing at
the quotient `4/3`. Two genuinely different test objects, one engine. -/
theorem icPathAdj_secondEval_le_testVector :
    secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 3)) ≤ 4 / 3 := by
  calc secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 3))
      ≤ rayleigh (normalizedLaplacian icPathAdj)
          (degreeSqrt icPathAdj *ᵥ
            cutTestVector icPathAdj ({0} : Finset (Fin 3))) :=
          secondEval_le_rayleigh_of_ker
            (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
            (normalizedLaplacian_psd icPathAdj icPathAdj_symmetric
              icPathAdj_nonneg icPathAdj_pos_deg)
            icPathAdj_kernelVec_ne
            (normalizedLaplacian_mulVec_degreeSqrt_onesVec icPathAdj
              icPathAdj_pos_deg)
            (by decide)
            (degreeSqrt_mulVec_cutTestVector_ne_zero icPathAdj
              icPathAdj_pos_deg (by decide) (by decide))
            (dotProduct_degreeSqrt_mulVec_cutTestVector icPathAdj
              (fun i => le_of_lt (icPathAdj_pos_deg i)) _)
    _ = 4 / 3 := icPathAdj_rayleigh

/-!
### The conductance side computed by hand
-/

/-- Complement equations for the six nonempty proper cuts of `Fin 3`
(evaluated by `decide`). -/
theorem ic_compl_0 : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
theorem ic_compl_1 : ({1} : Finset (Fin 3))ᶜ = {0, 2} := by decide
theorem ic_compl_2 : ({2} : Finset (Fin 3))ᶜ = {0, 1} := by decide
theorem ic_compl_01 : ({0, 1} : Finset (Fin 3))ᶜ = {2} := by decide
theorem ic_compl_02 : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide
theorem ic_compl_12 : ({1, 2} : Finset (Fin 3))ᶜ = {0} := by decide

/-- The three degree values as standalone rewrites. -/
theorem ic_deg_0 : deg icPathAdj 0 = 1 := by
  simp [icPathAdj_deg]
theorem ic_deg_1 : deg icPathAdj 1 = 2 := by
  simp [icPathAdj_deg]
theorem ic_deg_2 : deg icPathAdj 2 = 1 := by
  simp [icPathAdj_deg]

/-- The volumes of the six nonempty proper cuts (degrees `1, 2, 1`). -/
theorem ic_vol_1 : vol icPathAdj ({1} : Finset (Fin 3)) = 2 := by
  rw [vol, Finset.sum_singleton, ic_deg_1]
theorem ic_vol_2 : vol icPathAdj ({2} : Finset (Fin 3)) = 1 := by
  rw [vol, Finset.sum_singleton, ic_deg_2]
theorem ic_vol_01 : vol icPathAdj ({0, 1} : Finset (Fin 3)) = 3 := by
  rw [vol, Finset.sum_insert (by decide), Finset.sum_singleton,
    ic_deg_0, ic_deg_1]
  norm_num
theorem ic_vol_02 : vol icPathAdj ({0, 2} : Finset (Fin 3)) = 2 := by
  rw [vol, Finset.sum_insert (by decide), Finset.sum_singleton,
    ic_deg_0, ic_deg_2]
  norm_num
theorem ic_vol_12 : vol icPathAdj ({1, 2} : Finset (Fin 3)) = 3 := by
  rw [vol, Finset.sum_insert (by decide), Finset.sum_singleton,
    ic_deg_1, ic_deg_2]
  norm_num

/-- The boundaries of the six nonempty proper cuts. -/
theorem ic_boundary_1 : boundary icPathAdj ({1} : Finset (Fin 3)) = 2 := by
  rw [boundary, ic_compl_1, Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [icPathAdj]
theorem ic_boundary_2 : boundary icPathAdj ({2} : Finset (Fin 3)) = 1 := by
  rw [boundary, ic_compl_2, Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [icPathAdj]
theorem ic_boundary_01 : boundary icPathAdj ({0, 1} : Finset (Fin 3)) = 1 := by
  rw [boundary, ic_compl_01, Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton]
  norm_num [icPathAdj]
theorem ic_boundary_02 : boundary icPathAdj ({0, 2} : Finset (Fin 3)) = 2 := by
  rw [boundary, ic_compl_02, Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton]
  norm_num [icPathAdj]
theorem ic_boundary_12 : boundary icPathAdj ({1, 2} : Finset (Fin 3)) = 1 := by
  rw [boundary, ic_compl_12, Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton]
  norm_num [icPathAdj]

/-- The six cut conductances, computed from the pinned boundary and
volume values. -/
theorem ic_cond_0 : conductance icPathAdj ({0} : Finset (Fin 3)) = 1 := by
  rw [conductance, icPathAdj_boundary_zero, icPathAdj_vol_zero, ic_compl_0,
    ic_vol_12, min_eq_left (by norm_num : (1 : ℝ) ≤ 3)]
  exact div_self one_ne_zero
theorem ic_cond_1 : conductance icPathAdj ({1} : Finset (Fin 3)) = 1 := by
  rw [conductance, ic_boundary_1, ic_vol_1, ic_compl_1, ic_vol_02,
    min_eq_left (by norm_num : (2 : ℝ) ≤ 2)]
  exact div_self two_ne_zero
theorem ic_cond_2 : conductance icPathAdj ({2} : Finset (Fin 3)) = 1 := by
  rw [conductance, ic_boundary_2, ic_vol_2, ic_compl_2, ic_vol_01,
    min_eq_left (by norm_num : (1 : ℝ) ≤ 3)]
  exact div_self one_ne_zero
theorem ic_cond_01 : conductance icPathAdj ({0, 1} : Finset (Fin 3)) = 1 := by
  rw [conductance, ic_boundary_01, ic_vol_01, ic_compl_01, ic_vol_2,
    min_eq_right (by norm_num : (1 : ℝ) ≤ 3)]
  exact div_self one_ne_zero
theorem ic_cond_02 : conductance icPathAdj ({0, 2} : Finset (Fin 3)) = 1 := by
  rw [conductance, ic_boundary_02, ic_vol_02, ic_compl_02, ic_vol_1,
    min_eq_right (by norm_num : (2 : ℝ) ≤ 2)]
  exact div_self two_ne_zero
theorem ic_cond_12 : conductance icPathAdj ({1, 2} : Finset (Fin 3)) = 1 := by
  rw [conductance, ic_boundary_12, ic_vol_12, ic_compl_12,
    icPathAdj_vol_zero, min_eq_right (by norm_num : (1 : ℝ) ≤ 3)]
  exact div_self one_ne_zero

/-- **Every nonempty proper cut of `P₃` has conductance exactly `1`** —
the boundary always equals the minority volume on this fixture. -/
theorem icPathAdj_conductance_all (S : Finset (Fin 3))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    conductance icPathAdj S = 1 := by
  fin_cases S
  · exact absurd hS (by decide)
  all_goals first
  | exact absurd hS (by decide)
  | exact absurd hSc (by decide)
  | simpa using ic_cond_0
  | simpa using ic_cond_1
  | simpa using ic_cond_2
  | simpa using ic_cond_01
  | simpa using ic_cond_02
  | simpa using ic_cond_12

/-- **The Cheeger constant of `P₃` is `1`**, computed by exhausting the
six nonempty proper cuts. -/
theorem icPathAdj_cheegerConstant : cheegerConstant icPathAdj = 1 := by
  have hset : {c : ℝ | ∃ S : Finset (Fin 3), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance icPathAdj S = c} = {1} := by
    ext c
    constructor
    · rintro ⟨S, hS, hSc, rfl⟩
      exact icPathAdj_conductance_all S hS hSc
    · rintro ⟨rfl⟩
      exact ⟨{0}, by decide, by decide, ic_cond_0⟩
  rw [cheegerConstant, hset]
  simp

/-- **The theorem's instantiation on the irregular fixture, joined with
the independent spectral bound**: the theorem gives `λ₂ ≤ 2 · 1 = 2`
through the stretched cut test vector; the eigenpair route gives the
strictly stronger `λ₂ ≤ 1`. The pair is coherent (the hand value sits
inside the theorem's bound) and non-circular (the `≤ 1` side never
touches the Cheeger theorem). -/
theorem icPathAdj_coherence :
    secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 3))
      ≤ 2 * cheegerConstant icPathAdj ∧
    secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 3)) ≤ 1 ∧
    cheegerConstant icPathAdj = 1 :=
  ⟨cheeger_upper_bound_normalized icPathAdj icPathAdj_symmetric
      icPathAdj_nonneg icPathAdj_pos_deg (by decide),
    icPathAdj_secondEval_le_one, icPathAdj_cheegerConstant⟩

/-!
## Regular recovery on K₂
-/

/-- On the regular cone the new theorem's spectral side *is* the regular
family's: `normalizedLaplacian edgeAdj = regularNormalizedLaplacian
edgeAdj 1`, and the delivered K₂ pin `λ₂ = 2` transports. -/
theorem icEdge_normLap_secondEval :
    secondEval (normalizedLaplacian edgeAdj)
        (normalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric)
        (le_refl 2)
      = 2 :=
  (secondEval_congr (normalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric)
    (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1)
    (le_refl 2)
    (normalizedLaplacian_eq_regularNormalizedLaplacian edgeAdj 1
      edgeAdj_regular (by norm_num))).trans
    edge_normLap_secondEval_eq_two_QA

/-- The tight recovery: the irregular theorem instantiates on `K₂` to
`2 ≤ 2 · 1` — the same tight statement the regular QA pinned, reached
through the degree-stretched route. -/
theorem icEdge_recovery :
    secondEval (normalizedLaplacian edgeAdj)
        (normalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric)
        (le_refl 2)
      = 2 * cheegerConstant edgeAdj := by
  rw [icEdge_normLap_secondEval, edge_cheegerConstant]
  norm_num

theorem icEdge_instantiation :
    secondEval (normalizedLaplacian edgeAdj)
        (normalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric)
        (le_refl 2)
      ≤ 2 * cheegerConstant edgeAdj :=
  cheeger_upper_bound_normalized edgeAdj edgeAdj_symmetric edgeAdj_nonneg
    (fun i => by rw [edgeAdj_regular i]; norm_num) (le_refl 2)

theorem icEdge_pos_deg : ∀ i, 0 < deg edgeAdj i := by
  intro i
  rw [edgeAdj_regular i]
  norm_num

/-!
## The PSD fence on the general-kernel engine
-/

/-- The fence matrix `diag(-1, 0)`: symmetric, `e₁` is a kernel vector,
`e₀ ⊥ e₁` — but it is *not* PSD, and the hypothesis-free conclusion
fails. -/
def icFenceAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 0)

theorem icFenceAdj_symmetric : icFenceAdj.IsSymm := by
  rw [icFenceAdj]
  exact Matrix.diagonal_transpose _

theorem icFenceAdj_apply (i j : Fin 2) :
    icFenceAdj i j = if i = j then (if i = 0 then -1 else 0) else 0 := by
  simp only [icFenceAdj, Matrix.diagonal_apply]

theorem icFenceAdj_mulVec_single_one :
    icFenceAdj *ᵥ (Pi.single (1 : Fin 2) (1 : ℝ)) = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, icFenceAdj,
      Fin.sum_univ_two, Pi.single_apply]

theorem icFenceAdj_single_zero_dot :
    Matrix.dotProduct (Pi.single (0 : Fin 2) (1 : ℝ)) (Pi.single (1 : Fin 2) (1 : ℝ)) = 0 := by
  simp [Matrix.dotProduct, Fin.sum_univ_two, Pi.single_apply]

theorem icFenceAdj_single_zero_ne : (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

theorem icFenceAdj_single_one_ne : (Pi.single (1 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 1
  simp at h0

/-- PSD fails at the witness: the quadratic form at `e₀` is `-1`. -/
theorem icFenceAdj_not_psd :
    ¬ (∀ x : Fin 2 → ℝ, 0 ≤ quadForm icFenceAdj x) := by
  intro hpsd
  have h0 := hpsd (Pi.single (0 : Fin 2) (1 : ℝ))
  have : quadForm icFenceAdj (Pi.single (0 : Fin 2) (1 : ℝ)) = -1 := by
    simp only [quadForm, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_two, icFenceAdj_apply, Pi.single_apply]
    norm_num
  rw [this] at h0
  linarith

/-- The Rayleigh quotient of `e₀` is `-1`. -/
theorem icFenceAdj_rayleigh :
    rayleigh icFenceAdj (Pi.single (0 : Fin 2) (1 : ℝ)) = -1 := by
  rw [rayleigh, if_neg icFenceAdj_single_zero_ne]
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_two, icFenceAdj_apply, Pi.single_apply]
  norm_num

/-- The trace and determinant of the fence matrix. -/
theorem icFenceAdj_trace : icFenceAdj.trace = -1 := by
  simp [Matrix.trace, icFenceAdj_apply, Fin.sum_univ_two]

theorem icFenceAdj_det : icFenceAdj.det = 0 := by
  simp [Matrix.det_fin_two, icFenceAdj_apply]


/-- A length-two list is the list of its two entries. -/
private theorem list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- Two-point sorted-list pin, second entry: a sorted length-two list
with sum `-1` and product `0` has second entry `0`. -/
private theorem icFence_two_point_pin {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = -1)
    (hprod : l.prod = 0) : l.get ⟨1, by omega⟩ = 0 := by
  obtain ⟨a, b, hl⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, list_two_eq h2⟩
  subst hl
  have hlt : (0 : Fin 2) < (1 : Fin 2) := by decide
  have hmono : a ≤ b := hs.rel_get_of_lt hlt
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  rw [List.get_cons_succ]
  show b = 0
  rcases mul_eq_zero.1 hprod with h0 | h1
  · linarith
  · exact h1

/-- The fence matrix's second sorted eigenvalue is `0` (sorted spectrum
`[-1, 0]`), by the trace/determinant pin. -/
theorem icFenceAdj_secondEval :
    secondEval icFenceAdj icFenceAdj_symmetric (le_refl 2) = 0 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm icFenceAdj_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm icFenceAdj_symmetric).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm icFenceAdj_symmetric).eigenvalues))).sum = -1 := by
    have htr : ∑ i : Fin 2, eigvalOf icFenceAdj icFenceAdj_symmetric i
        = -1 := by
      rw [eigvalOf_sum_eq_trace, icFenceAdj_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm icFenceAdj_symmetric).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2,
        ((isHermitian_of_isSymm icFenceAdj_symmetric).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm icFenceAdj_symmetric).det_eq_prod_eigenvalues
      rw [icFenceAdj_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact icFence_two_point_pin hlen hsorted hsum hprod

/-- **The PSD fence, refuted in proved form**: with every hypothesis of
`secondEval_le_rayleigh_of_ker` except `hpsd` verified on the fixture
(`hM`, `hwne`, `hker`, `hcard`, `hx0`, `hxorth` — see the lemmas above),
the conclusion `secondEval ≤ rayleigh` reads `0 ≤ -1` and is false.
Exactly `hpsd` is isolated (`icFenceAdj_not_psd`). -/
theorem icFence_psd_fence :
    ¬ (secondEval icFenceAdj icFenceAdj_symmetric (le_refl 2)
        ≤ rayleigh icFenceAdj (Pi.single (0 : Fin 2) (1 : ℝ))) := by
  rw [icFenceAdj_secondEval, icFenceAdj_rayleigh]
  norm_num

/-!
## The degree fence on the headline theorem
-/

/-- The all-zero adjacency on `Fin 2`: symmetric, nonnegative, two
vertices — and every degree is `0`, so the theorem's positive-degree
hypothesis fails. -/
def icZeroAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 0, 0]

theorem icZeroAdj_symmetric : icZeroAdj.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [icZeroAdj]

theorem icZeroAdj_nonneg : ∀ i j, 0 ≤ icZeroAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [icZeroAdj]

theorem icZeroAdj_deg : ∀ i, deg icZeroAdj i = 0 := by
  intro i
  fin_cases i <;> simp [deg, icZeroAdj, Fin.sum_univ_two]

/-- With all degrees zero, the normalized Laplacian is exactly the
identity (the adjacency term vanishes regardless of the junk reciprocal
square roots). -/
theorem icZeroAdj_normLap :
    normalizedLaplacian icZeroAdj
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hz : icZeroAdj = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [icZeroAdj]
  rw [hz]
  simp [normalizedLaplacian]

/-- Every conductance is junk-zero: `boundary = 0` (no edges) and both
volumes are `0`, so `0 / min 0 0 = 0`. -/
theorem icZeroAdj_conductance (S : Finset (Fin 2)) (_hS : S.Nonempty)
    (_hSc : Sᶜ.Nonempty) : conductance icZeroAdj S = 0 := by
  have hz : ∀ i j : Fin 2, icZeroAdj i j = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [icZeroAdj]
  have hd : ∀ i, deg icZeroAdj i = 0 := by
    intro i
    fin_cases i <;> simp [deg, icZeroAdj, Fin.sum_univ_two]
  have hb : boundary icZeroAdj S = 0 := by
    simp only [boundary]
    exact Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => hz i j
  have hv : vol icZeroAdj S = 0 := by
    simp only [vol]
    exact Finset.sum_eq_zero fun i _ => hd i
  have hvc : vol icZeroAdj Sᶜ = 0 := by
    simp only [vol]
    exact Finset.sum_eq_zero fun i _ => hd i
  rw [conductance, hb, hv, hvc]
  norm_num

theorem icZeroAdj_cheegerConstant : cheegerConstant icZeroAdj = 0 := by
  have hset : {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance icZeroAdj S = c} = {0} := by
    ext c
    constructor
    · rintro ⟨S, hS, hSc, rfl⟩
      exact icZeroAdj_conductance S hS hSc
    · rintro ⟨rfl⟩
      exact ⟨{0}, by decide, by decide, icZeroAdj_conductance _
        (by decide) (by decide)⟩
  rw [cheegerConstant, hset]
  simp

/-- Trace and determinant of the identity. -/
theorem one_trace : (1 : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 := by
  simp [Matrix.trace, Matrix.one_apply, Fin.sum_univ_two]

theorem one_det : (1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [Matrix.det_fin_two, Matrix.one_apply]
  norm_num

/-- Two-point sorted-list pin, second entry: a sorted length-two list
with sum `2` and product `1` has second entry `1`. -/
private theorem icOne_two_point_pin {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = 2)
    (hprod : l.prod = 1) : l.get ⟨1, by omega⟩ = 1 := by
  obtain ⟨a, b, hl⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, list_two_eq h2⟩
  subst hl
  have hlt : (0 : Fin 2) < (1 : Fin 2) := by decide
  have hmono : a ≤ b := hs.rel_get_of_lt hlt
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  rw [List.get_cons_succ]
  show b = 1
  have hb : b = 2 - a := by linarith
  rw [hb] at hprod ⊢
  have hsq : (a - 1) ^ 2 = 0 := by
    linear_combination -hprod
  have ha1 : a - 1 = 0 := by
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  linarith

/-- The second sorted eigenvalue of the identity is `1` — by the
trace/determinant pin (sorted spectrum `[1, 1]`). -/
theorem one_isSymm' : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_one]

theorem one_secondEval :
    secondEval (1 : Matrix (Fin 2) (Fin 2) ℝ) one_isSymm'
        (le_refl 2) = 1 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm
          (one_isSymm' : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm
          (one_isSymm' : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm
          (one_isSymm' : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues))).sum = 2 := by
    have htr : ∑ i : Fin 2,
        eigvalOf (1 : Matrix (Fin 2) (Fin 2) ℝ) one_isSymm' i = 2 := by
      rw [eigvalOf_sum_eq_trace, one_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm
          (one_isSymm' : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues))).prod = 1 := by
    have hd : ∏ i : Fin 2,
        ((isHermitian_of_isSymm one_isSymm').eigenvalues i) = 1 := by
      have hd0 := (isHermitian_of_isSymm one_isSymm').det_eq_prod_eigenvalues
      rw [one_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact icOne_two_point_pin hlen hsorted hsum hprod

theorem icZeroAdj_secondEval :
    secondEval (normalizedLaplacian icZeroAdj)
        (normalizedLaplacian_symmetric icZeroAdj icZeroAdj_symmetric)
        (le_refl 2) = 1 :=
  (secondEval_congr (normalizedLaplacian_symmetric icZeroAdj icZeroAdj_symmetric)
    one_isSymm' (le_refl 2)
    icZeroAdj_normLap).trans one_secondEval

/-- **The degree fence, refuted in proved form**: with every hypothesis
of `cheeger_upper_bound_normalized` except `hd : ∀ i, 0 < deg A i`
verified on the all-zero fixture (`hA`, `hnonneg`, `hcard` — see the
lemmas above; each degree is `0` by `icZeroAdj_deg`), the conclusion
reads `1 ≤ 2 · 0` and is false: the spectral side is the identity's
`λ₂ = 1` while every conductance is junk-zero. Exactly the
positive-degree hypothesis is isolated. -/
theorem icZero_degree_fence :
    ¬ (secondEval (normalizedLaplacian icZeroAdj)
        (normalizedLaplacian_symmetric icZeroAdj icZeroAdj_symmetric)
        (le_refl 2)
      ≤ 2 * cheegerConstant icZeroAdj) := by
  rw [icZeroAdj_secondEval, icZeroAdj_cheegerConstant]
  norm_num

end SpectralGraphTheory.QA
