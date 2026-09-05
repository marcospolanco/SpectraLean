/-
  IrregularCheeger_QA.lean

  Purpose
  -------
  QA for the irregular Cheeger inequalities delivered in
  `Scaffold.Mathlib.GraphTheory.VariationalTransfer` (proposal
  `proposals/irregular-cheeger-variational-transfer.md`, 2026-08-25):
  the easy direction `cheeger_upper_bound_normalized` —
  `secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A` — and,
  since 2026-08-25/26, the hard direction
  `cheeger_lower_bound_normalized` —
  `cheegerConstant A ^ 2 / 2 ≤ secondEval (normalizedLaplacian A)` —
  both on arbitrary symmetric nonnegative positive-degree graphs,
  together with their engines: the general-kernel variational lemmas
  (`secondEval_le_rayleigh_of_ker`, `secondEval_variational_of_ker` in
  `Scaffold.Mathlib.GraphTheory.Spectral`), the degree-stretched
  cut-test-vector layer, and the `VolumeHardDirection` machinery of
  `Scaffold.Mathlib.GraphTheory.Cheeger` (the volume median, the
  degree-weighted co-area core, the per-part bound, the weighted norm
  split, the f-level sweep lemma).

  Sections:

  - **The irregular Fiedler instantiation QA (2026-08-26)**: the exact
    spectral pin `λ₂ (L_sym P₃) = 1` (the new `≥ 1` side by the
    sum-of-squares `2 x₁²` through the sInf engine, joined to the
    pre-existing eigenpair `≤ 1` side), the capstone theorem's
    instances on `P₃` (against the exact pin and the exhaustive-cut
    pin) and on `K₂` (against the pinned classical `λ₂ = 2`, the
    regular family's own constant on the cone), the stretch
    cancellation and the constraint hinge verified raw at the concrete
    eigenpair witness, and the connectivity mechanism fenced on the
    disconnected fixture (`λ₂ = 0` pinned; a kernel eigenvector
    provably violates the orthogonality hinge the constraint
    conversion needs — `0 < λ₂`, not kernel-ness, is what connectivity
    supplies).

  - **The volume-weighted sweep-cut extraction QA (2026-08-26)**: the
    extraction witness *forced* on irregular input (the level
    membership iff pins the returned set to `{0}` on `P₃` at
    `y = ![1,0,0]`, conductance `1` against the bound `2/1` both sides
    raw), the sweep instances on the pair's shared cut test vector
    (the family characterized in-instance, `1 ≤ 8/3` at the pinned
    `R = 4/3`) and on `K₂` (`1 ≤ 4` at the pinned `R = 2`), and the
    degree-weighted zero-sum fence refuting the hypothesis-dropped
    conclusion in proved form (`f = ![1,2]`: `1 ≤ 2/5` false for every
    swept candidate, `R = 1/5` computed raw).

  - **The connectivity-transfer QA (2026-08-26)**: the P₃/K₂ positive
    instances joined to the file's independent spectral pins, the
    kernel iff exercised both directions, the disconnected two-edge
    negative witness (`λ₂ = 0` by two independent routes), and the
    `hconn`/`hnn` fences in proved form (the signed fixture is
    *connected*, isolating `hnn` exactly).
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

  - **Regular recovery on `K₂`** (`cheegerEdgeAdj`, reused from `Cheeger_QA` by
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

  - **The hard direction (2026-08-25/26)**: the volume
    median forced to its unique value `-1` on the shared `P₃` cut test
    vector (both containment steps through `vol_le_vol_of_subset`), the
    weighted norm-split identity `16 + 0 = 12 + 1 · 4` with the
    remainder visible, the `K₂` volume co-area equality pin (both sides
    `2`), the per-part pin `1 ≤ 2`, the sweep instances on both fixtures
    (`1/2 ≤ 2` raw; `1/2 ≤ 4/3` at the same test vector the easy
    direction consumes), both Cheeger inequalities holding
    simultaneously on `P₃` against the independently pinned spectral
    bracket, the `K₂` regular recovery matching the regular family's
    own bound, and two proved fences — the volume-minority drop
    (`4 ≤ 0` refuted) and the signed-weights refutation isolating
    `hnn` (`!![2, -1; -1, 2]`: every other hypothesis verified,
    `λ₂ = 0` by the trace/determinant pin, `φ = -1` by both-cuts
    computation, conclusion `1/2 ≤ 0` false).

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
family's: `normalizedLaplacian cheegerEdgeAdj = regularNormalizedLaplacian
cheegerEdgeAdj 1`, and the delivered K₂ pin `λ₂ = 2` transports. -/
theorem icEdge_normLap_secondEval :
    secondEval (normalizedLaplacian cheegerEdgeAdj)
        (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        (le_refl 2)
      = 2 :=
  (secondEval_congr (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
    (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
    (le_refl 2)
    (normalizedLaplacian_eq_regularNormalizedLaplacian cheegerEdgeAdj 1
      cheegerEdgeAdj_regular (by norm_num))).trans
    edge_normLap_secondEval_eq_two_QA

/-- The tight recovery: the irregular theorem instantiates on `K₂` to
`2 ≤ 2 · 1` — the same tight statement the regular QA pinned, reached
through the degree-stretched route. -/
theorem icEdge_recovery :
    secondEval (normalizedLaplacian cheegerEdgeAdj)
        (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        (le_refl 2)
      = 2 * cheegerConstant cheegerEdgeAdj := by
  rw [icEdge_normLap_secondEval, edge_cheegerConstant]
  norm_num

theorem icEdge_instantiation :
    secondEval (normalizedLaplacian cheegerEdgeAdj)
        (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        (le_refl 2)
      ≤ 2 * cheegerConstant cheegerEdgeAdj :=
  cheeger_upper_bound_normalized cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg
    (fun i => by rw [cheegerEdgeAdj_regular i]; norm_num) (le_refl 2)

theorem icEdge_pos_deg : ∀ i, 0 < deg cheegerEdgeAdj i := by
  intro i
  rw [cheegerEdgeAdj_regular i]
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

/-!
## The hard direction (delivered 2026-08-25/26)

`cheeger_lower_bound_normalized` and its `VolumeHardDirection` engine
chain (`exists_median_vol`, `boundary_ge_of_minority_vol`,
`coarea_core_vol`, `hardDirection_perPart_vol`,
`median_parts_norm_vol`, `cheeger_sweep_normalized`,
`secondEval_variational_of_ker`): the same irregular fixtures pin the
new layers, both Cheeger inequalities are checked to hold
simultaneously on `P₃` against the independently pinned spectral
bracket, the regular recovery on `K₂` agrees with the regular family's
own bound, and the proved fences isolate the volume-minority and
nonnegativity hypotheses.
-/

/-- Entry bounds of the shared cut test vector. -/
theorem ichv_cutVec_ge (i : Fin 3) :
    -1 ≤ cutTestVector icPathAdj ({0} : Finset (Fin 3)) i := by
  rw [icPathAdj_cutVec]
  fin_cases i <;> (try simp; try norm_num)

theorem ichv_cutVec_gt : -1 < cutTestVector icPathAdj ({0} : Finset (Fin 3)) 0 := by
  rw [icPathAdj_cutVec]
  simp
  norm_num

theorem ichv_cutVec_eq_of_ne {i : Fin 3} (hi : i ≠ 0) :
    cutTestVector icPathAdj ({0} : Finset (Fin 3)) i = -1 := by
  rw [icPathAdj_cutVec]
  fin_cases i
  · exact absurd rfl hi
  · rfl
  · rfl

/-- **The volume median is forced**: on `P₃` at the shared cut test
vector `![3, -1, -1]` (degrees `1, 2, 1`, total volume `4`), every
volume median is exactly `-1` — above `-1` the strict lower set
`{1, 2}` already carries volume `3`, violating the lower count; below
`-1` the strict upper set is everything, violating the upper count.
The containment steps are `vol_le_vol_of_subset` doing real work. -/
theorem ichv_median_pin_QA :
    ∀ m : ℝ,
      2 * vol icPathAdj (Finset.univ.filter (fun i => m < cutTestVector icPathAdj ({0} : Finset (Fin 3)) i))
        ≤ vol icPathAdj (Finset.univ : Finset (Fin 3))
        ∧ 2 * vol icPathAdj (Finset.univ.filter (fun i => cutTestVector icPathAdj ({0} : Finset (Fin 3)) i < m))
          ≤ vol icPathAdj (Finset.univ : Finset (Fin 3)) →
      m = -1 := by
  intro m ⟨hup, hlow⟩
  rcases lt_trichotomy m (-1) with h | h | h
  · exfalso
    have hsub : (Finset.univ : Finset (Fin 3))
        ⊆ Finset.univ.filter (fun i => m < cutTestVector icPathAdj ({0} : Finset (Fin 3)) i) := by
      intro i _
      exact Finset.mem_filter.2 ⟨Finset.mem_univ i, lt_of_lt_of_le h (ichv_cutVec_ge i)⟩
    have h1 : vol icPathAdj (Finset.univ : Finset (Fin 3))
        ≤ vol icPathAdj (Finset.univ.filter
          (fun i => m < cutTestVector icPathAdj ({0} : Finset (Fin 3)) i)) :=
      vol_le_vol_of_subset icPathAdj icPathAdj_nonneg hsub
    rw [icPathAdj_vol_univ] at hup h1
    linarith
  · exact h
  · exfalso
    have hsub : ({1, 2} : Finset (Fin 3))
        ⊆ Finset.univ.filter (fun i => cutTestVector icPathAdj ({0} : Finset (Fin 3)) i < m) := by
      intro i hi
      refine Finset.mem_filter.2 ⟨Finset.mem_univ i, ?_⟩
      rw [ichv_cutVec_eq_of_ne (by
        intro h0
        have h02 : (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by
          rw [← h0]
          exact hi
        exact absurd h02 (by decide))]
      exact h
    have h1 : vol icPathAdj ({1, 2} : Finset (Fin 3))
        ≤ vol icPathAdj (Finset.univ.filter
          (fun i => cutTestVector icPathAdj ({0} : Finset (Fin 3)) i < m)) :=
      vol_le_vol_of_subset icPathAdj icPathAdj_nonneg hsub
    rw [icPathAdj_vol_univ] at hlow
    have h2 : vol icPathAdj ({1, 2} : Finset (Fin 3)) = 3 := ic_vol_12
    linarith

/-- The forced volume median exists and the forcing is nonvacuous: the
hypothesis set is inhabited (the delivered `exists_median_vol`), and
combined with the pin above the median is uniquely `-1`. -/
theorem ichv_median_forced_QA :
    ∃ m : ℝ,
      2 * vol icPathAdj (Finset.univ.filter (fun i => m < cutTestVector icPathAdj ({0} : Finset (Fin 3)) i))
        ≤ vol icPathAdj (Finset.univ : Finset (Fin 3))
        ∧ 2 * vol icPathAdj (Finset.univ.filter (fun i => cutTestVector icPathAdj ({0} : Finset (Fin 3)) i < m))
          ≤ vol icPathAdj (Finset.univ : Finset (Fin 3))
        ∧ m = -1 :=
  let ⟨m, h1, h2⟩ := exists_median_vol icPathAdj icPathAdj_nonneg
    (cutTestVector icPathAdj ({0} : Finset (Fin 3)))
  ⟨m, h1, h2, ichv_median_pin_QA m ⟨h1, h2⟩⟩

/-- The degree-weighted zero sum of the shared cut test vector, in the
form the hard-direction chain consumes. -/
theorem ichv_cutVec_weighted_sum :
    ∑ i, deg icPathAdj i * cutTestVector icPathAdj ({0} : Finset (Fin 3)) i
      = 0 := by
  rw [← dotProduct_degreeSqrt_mulVec_onesVec icPathAdj
    (fun i => le_of_lt (icPathAdj_pos_deg i))]
  exact dotProduct_degreeSqrt_mulVec_cutTestVector icPathAdj
    (fun i => le_of_lt (icPathAdj_pos_deg i)) _

/-- The shifted part sums at the forced median: `(f - (-1))⁺` carries
`16 = 1 · 4²` and `(f - (-1))⁻` carries `0`. -/
theorem ichv_norm_split_parts :
    ∑ i, deg icPathAdj i * (max (cutTestVector icPathAdj ({0} : Finset (Fin 3)) i - (-1)) 0) ^ 2
      = 16
      ∧ ∑ i, deg icPathAdj i * (max ((-1) - cutTestVector icPathAdj ({0} : Finset (Fin 3)) i) 0) ^ 2
        = 0 := by
  have hpos : ∀ i : Fin 3,
      max (cutTestVector icPathAdj ({0} : Finset (Fin 3)) i - (-1)) 0
        = cutTestVector icPathAdj ({0} : Finset (Fin 3)) i - (-1) := by
    intro i
    exact max_eq_left (by linarith [ichv_cutVec_ge i])
  have hneg : ∀ i : Fin 3,
      max ((-1) - cutTestVector icPathAdj ({0} : Finset (Fin 3)) i) 0 = 0 := by
    intro i
    exact max_eq_right (by linarith [ichv_cutVec_ge i])
  have hs1 : ∑ i, deg icPathAdj i
        * (max (cutTestVector icPathAdj ({0} : Finset (Fin 3)) i - (-1)) 0) ^ 2
      = ∑ i, deg icPathAdj i
          * (cutTestVector icPathAdj ({0} : Finset (Fin 3)) i - (-1)) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hpos i]
  have hs2 : ∑ i, deg icPathAdj i
        * (max ((-1) - cutTestVector icPathAdj ({0} : Finset (Fin 3)) i) 0) ^ 2
      = ∑ i, deg icPathAdj i * (0 : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hneg i]
  rw [hs1, hs2, icPathAdj_cutVec]
  constructor
  · simp [icPathAdj_deg, Fin.sum_univ_three]
    norm_num
  · simp

/-- The weighted norm of the cut test vector: `9 + 2 + 1 = 12`. -/
theorem ichv_weighted_norm :
    ∑ i, deg icPathAdj i * cutTestVector icPathAdj ({0} : Finset (Fin 3)) i ^ 2
      = 12 := by
  rw [icPathAdj_cutVec]
  simp [icPathAdj_deg, Fin.sum_univ_three]
  norm_num

/-- **The volume-median norm split on the same fixture**: at `f` the
cut test vector and `m = -1`, the identity behind
`median_parts_norm_vol` reads `16 + 0 = 12 + 1 · 4` — the `m² · vol V`
remainder visible. -/
theorem ichv_norm_split_pin_QA :
    ∑ i, deg icPathAdj i * (max (cutTestVector icPathAdj ({0} : Finset (Fin 3)) i - (-1)) 0) ^ 2
      + ∑ i, deg icPathAdj i * (max ((-1) - cutTestVector icPathAdj ({0} : Finset (Fin 3)) i) 0) ^ 2
      = 16
      ∧ ∑ i, deg icPathAdj i * cutTestVector icPathAdj ({0} : Finset (Fin 3)) i ^ 2
        + (-1) ^ 2 * vol icPathAdj (Finset.univ : Finset (Fin 3)) = 16 := by
  rw [ichv_norm_split_parts.1, ichv_norm_split_parts.2, ichv_weighted_norm,
    icPathAdj_vol_univ]
  norm_num

/-- The norm split as an instance of the theorem (not just the pinned
numbers): `median_parts_norm_vol` at the forced median. -/
theorem ichv_norm_split_instance_QA :
    ∑ i, deg icPathAdj i * cutTestVector icPathAdj ({0} : Finset (Fin 3)) i ^ 2
      ≤ ∑ i, deg icPathAdj i * (max (cutTestVector icPathAdj ({0} : Finset (Fin 3)) i - (-1)) 0) ^ 2
        + ∑ i, deg icPathAdj i * (max ((-1) - cutTestVector icPathAdj ({0} : Finset (Fin 3)) i) 0) ^ 2 :=
  median_parts_norm_vol icPathAdj icPathAdj_nonneg (m := -1) ichv_cutVec_weighted_sum

/-!
### The co-area core and the per-part bound on `K₂`
-/

theorem ichv_edge_pos_deg : ∀ i, 0 < deg cheegerEdgeAdj i := by
  intro i
  rw [cheegerEdgeAdj_regular]
  norm_num

theorem ichv_edge_vol_univ :
    vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2)) = 2 := by
  rw [vol, Finset.sum_congr rfl (fun i _ => cheegerEdgeAdj_regular i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- The minority hypothesis of the volume co-area at `y = ![1, 0]` on
`K₂`: every positive-level closed superlevel set sits inside the
minority singleton `{0}`. -/
theorem ichv_edge_minority (t : ℝ) (ht : 0 < t) :
    2 * vol cheegerEdgeAdj
        (Finset.univ.filter (fun i : Fin 2 => t ≤ (![1, 0] : Fin 2 → ℝ) i ^ 2))
      ≤ vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2)) := by
  have hsub : Finset.univ.filter (fun i : Fin 2 => t ≤ (![1, 0] : Fin 2 → ℝ) i ^ 2)
      ⊆ ({0} : Finset (Fin 2)) := by
    intro i hi
    have hmem := (Finset.mem_filter.1 hi).2
    fin_cases i
    · exact Finset.mem_singleton.2 rfl
    · exfalso
      norm_num [Matrix.cons_val_one, Matrix.head_cons] at hmem
      linarith
  have h1 : vol cheegerEdgeAdj
      (Finset.univ.filter (fun i : Fin 2 => t ≤ (![1, 0] : Fin 2 → ℝ) i ^ 2))
      ≤ vol cheegerEdgeAdj ({0} : Finset (Fin 2)) :=
    vol_le_vol_of_subset cheegerEdgeAdj cheegerEdgeAdj_nonneg hsub
  obtain ⟨hv1, -⟩ := edge_vol_singleton 0
  rw [ichv_edge_vol_univ]
  linarith

/-- **The volume co-area equality pin on `K₂`**: at `y = ![1, 0]` both
sides compute to `2` (LHS `2 · (φ · ∑ deg y²) = 2 · (1 · 1)`, RHS the
total variation `2` of `y²` across the edge) — the layer-cake constant
exactly attained. -/
theorem ichv_coarea_edge_eq_QA :
    2 * (cheegerConstant cheegerEdgeAdj * ∑ i, deg cheegerEdgeAdj i * (![1, 0] : Fin 2 → ℝ) i ^ 2)
      = 2
      ∧ ∑ i, ∑ j, cheegerEdgeAdj i j * |(![1, 0] : Fin 2 → ℝ) i ^ 2 - (![1, 0] : Fin 2 → ℝ) j ^ 2|
        = 2 := by
  constructor
  · rw [edge_cheegerConstant, Fin.sum_univ_two, cheegerEdgeAdj_regular 0,
      cheegerEdgeAdj_regular 1]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · norm_num [Matrix.mul_apply, cheegerEdgeAdj, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply]

/-- The co-area theorem's instance on the same fixture, through the
delivered statement (not just the pinned numbers). -/
theorem ichv_coarea_edge_instance_QA :
    2 * (cheegerConstant cheegerEdgeAdj * ∑ i, deg cheegerEdgeAdj i * (![1, 0] : Fin 2 → ℝ) i ^ 2)
      ≤ ∑ i, ∑ j, cheegerEdgeAdj i j * |(![1, 0] : Fin 2 → ℝ) i ^ 2 - (![1, 0] : Fin 2 → ℝ) j ^ 2| := by
  rw [ichv_coarea_edge_eq_QA.1, ichv_coarea_edge_eq_QA.2]

/-- **The per-part bound pin on `K₂`**: `φ² · ∑ deg y² = 1 ≤ E'(y) = 2`
at `y = ![1, 0]`, both sides raw. -/
theorem ichv_perPart_edge_QA :
    cheegerConstant cheegerEdgeAdj ^ 2 * ∑ i, deg cheegerEdgeAdj i * (![1, 0] : Fin 2 → ℝ) i ^ 2
      ≤ ∑ i, ∑ j, cheegerEdgeAdj i j * ((![1, 0] : Fin 2 → ℝ) i - (![1, 0] : Fin 2 → ℝ) j) ^ 2
      ∧ cheegerConstant cheegerEdgeAdj ^ 2 * ∑ i, deg cheegerEdgeAdj i * (![1, 0] : Fin 2 → ℝ) i ^ 2 = 1
      ∧ ∑ i, ∑ j, cheegerEdgeAdj i j * ((![1, 0] : Fin 2 → ℝ) i - (![1, 0] : Fin 2 → ℝ) j) ^ 2 = 2 := by
  refine ⟨hardDirection_perPart_vol cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg
      ichv_edge_pos_deg _ (fun t ht => ichv_edge_minority t ht), ?_, ?_⟩
  · rw [edge_cheegerConstant, Fin.sum_univ_two, cheegerEdgeAdj_regular 0,
      cheegerEdgeAdj_regular 1]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · norm_num [Matrix.mul_apply, cheegerEdgeAdj, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply]

/-!
### The sweep lemma and the headline
-/

/-- The stretched test vector on `K₂` is the un-stretched one (all
degrees `1`). -/
theorem ichv_edge_stretch (f : Fin 2 → ℝ) :
    degreeSqrt cheegerEdgeAdj *ᵥ f = f := by
  funext i
  rw [degreeSqrt_mulVec]
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.diagonal_mul,
    mul_one, Matrix.diagonal_apply, cheegerEdgeAdj_regular, Real.sqrt_one,
    one_mul]

/-- **The sweep lemma on `K₂`**: at `f = ![1, -1]` (degree-weighted zero
sum `1 - 1 = 0`), `φ²/2 = 1/2 ≤ R_{L_sym}(f) = 2`, the quotient
computed raw against the independently pinned `λ₂ = 2`. -/
theorem ichv_sweep_edge_QA :
    cheegerConstant cheegerEdgeAdj ^ 2 / 2
      ≤ rayleigh (normalizedLaplacian cheegerEdgeAdj)
          (degreeSqrt cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))
      ∧ rayleigh (normalizedLaplacian cheegerEdgeAdj)
          (degreeSqrt cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))
        = 2 := by
  have horth : ∑ i, deg cheegerEdgeAdj i * (![1, -1] : Fin 2 → ℝ) i = 0 := by
    rw [Fin.sum_univ_two, cheegerEdgeAdj_regular 0, cheegerEdgeAdj_regular 1]
    norm_num
  have hne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, -1] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  refine ⟨cheeger_sweep_normalized cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg
    ichv_edge_pos_deg hne horth, ?_⟩
  have hmv : cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ) = ![-1, 1] := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, cheegerEdgeAdj, Fin.sum_univ_two]
  have hmul : normalizedLaplacian cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)
      = (2 : ℝ) • (![1, -1] : Fin 2 → ℝ) := by
    rw [normalizedLaplacian_eq_regularNormalizedLaplacian cheegerEdgeAdj 1
      cheegerEdgeAdj_regular (by norm_num), regularNormalizedLaplacian,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
      inv_one, one_smul, hmv]
    funext i
    fin_cases i <;> simp <;> norm_num
  have hdot : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) (![1, -1] : Fin 2 → ℝ)
      = 2 := by
    norm_num [Matrix.dotProduct, Fin.sum_univ_two]
  rw [ichv_edge_stretch, rayleigh, if_neg hne, quadForm, hmul,
    Matrix.dotProduct_smul, smul_eq_mul, hdot]
  norm_num

/-- **The hard bound on `P₃`**, joined with the independent spectral
bracket: the theorem gives `φ²/2 = 1/2 ≤ λ₂` at the pinned conductance
`φ = 1`; the easy direction's eigenpair witness gives the strictly
stronger `λ₂ ≤ 1`; and the pinned conductance completes the record.
Every side is derived from a different engine (volume co-area sweep,
eigenpair variational, hand-computed conductance) and they agree. -/
theorem ichv_p3_hard_bound_QA :
    cheegerConstant icPathAdj ^ 2 / 2
      ≤ secondEval (normalizedLaplacian icPathAdj)
          (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
          (by decide : 2 ≤ Fintype.card (Fin 3))
      ∧ secondEval (normalizedLaplacian icPathAdj)
          (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
          (by decide : 2 ≤ Fintype.card (Fin 3)) ≤ 1
      ∧ cheegerConstant icPathAdj ^ 2 / 2 = 1 / 2
      ∧ cheegerConstant icPathAdj = 1 := by
  refine ⟨cheeger_lower_bound_normalized icPathAdj icPathAdj_symmetric
      icPathAdj_nonneg icPathAdj_pos_deg (by decide),
    icPathAdj_secondEval_le_one, ?_, icPathAdj_cheegerConstant⟩
  rw [icPathAdj_cheegerConstant]
  norm_num

/-- **The sweep lemma instance on `P₃`**: the same cut test vector the
easy direction consumed, now through the hard direction's sweep lemma —
`φ²/2 = 1/2 ≤ R(√D · x) = 4/3`, the quotient already pinned by the
easy-direction section. One test object, both bounds. -/
theorem ichv_sweep_p3_QA :
    cheegerConstant icPathAdj ^ 2 / 2
      ≤ rayleigh (normalizedLaplacian icPathAdj)
          (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
      ∧ rayleigh (normalizedLaplacian icPathAdj)
          (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj ({0} : Finset (Fin 3)))
        = 4 / 3 := by
  have hcvne : cutTestVector icPathAdj ({0} : Finset (Fin 3)) ≠ 0 := by
    intro h
    have h0 : cutTestVector icPathAdj ({0} : Finset (Fin 3)) 0 = 0 :=
      congrFun h 0
    rw [icPathAdj_cutVec] at h0
    simp at h0
  exact ⟨cheeger_sweep_normalized icPathAdj icPathAdj_symmetric
      icPathAdj_nonneg icPathAdj_pos_deg hcvne ichv_cutVec_weighted_sum,
    icPathAdj_rayleigh⟩

/-- **The regular recovery on `K₂`**: the irregular theorem's conclusion
is `1/2 ≤ λ₂ = 2` — numerically identical to the regular family's own
`cheeger_lower_bound` instance on the same fixture, through the cone
agreement (`λ₂ (normalizedLaplacian cheegerEdgeAdj) = 2` already pinned via
`regularNormalizedLaplacian`). Route independence: both families, one
number. -/
theorem ichv_k2_regular_recovery_QA :
    cheegerConstant cheegerEdgeAdj ^ 2 / 2
      ≤ secondEval (normalizedLaplacian cheegerEdgeAdj)
          (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          (le_refl 2)
      ∧ secondEval (normalizedLaplacian cheegerEdgeAdj)
          (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          (le_refl 2) = 2
      ∧ cheegerConstant cheegerEdgeAdj ^ 2 / 2
        ≤ secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
          (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
          (le_refl 2) := by
  refine ⟨cheeger_lower_bound_normalized cheegerEdgeAdj cheegerEdgeAdj_symmetric
      cheegerEdgeAdj_nonneg ichv_edge_pos_deg (le_refl 2), icEdge_normLap_secondEval,
    ?_⟩
  exact cheeger_lower_bound cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg 1
    cheegerEdgeAdj_regular (by norm_num) cheegerEdgeAdj_card

/-!
### Fences
-/

/-- **The minority fence on the volume co-area core**: at `y = 1` on
`K₂` the minority hypothesis fails at the positive level `t = 1` (the
closed superlevel set is all of `V`), and the conclusion is refuted in
proved form — `4 ≤ 0` is false. Exactly the hypothesis `hy` is
isolated: the weights, symmetry, and degrees are all as in the equality
pin above. -/
theorem ichv_coarea_minority_fence_QA :
    ¬ (∀ t : ℝ, 0 < t →
        2 * vol cheegerEdgeAdj
            (Finset.univ.filter (fun i : Fin 2 => t ≤ (![1, 1] : Fin 2 → ℝ) i ^ 2))
          ≤ vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2)))
      ∧ 2 * (cheegerConstant cheegerEdgeAdj * ∑ i, deg cheegerEdgeAdj i * (![1, 1] : Fin 2 → ℝ) i ^ 2)
          = 4
      ∧ ∑ i, ∑ j, cheegerEdgeAdj i j * |(![1, 1] : Fin 2 → ℝ) i ^ 2 - (![1, 1] : Fin 2 → ℝ) j ^ 2|
          = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 := h 1 (by norm_num)
    have hfil : Finset.univ.filter (fun i : Fin 2 => (1:ℝ) ≤ (![1, 1] : Fin 2 → ℝ) i ^ 2)
        = (Finset.univ : Finset (Fin 2)) := by
      ext i
      fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hfil, ichv_edge_vol_univ] at h1
    norm_num at h1
  · rw [edge_cheegerConstant, Fin.sum_univ_two, cheegerEdgeAdj_regular 0,
      cheegerEdgeAdj_regular 1]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · norm_num [Matrix.mul_apply, cheegerEdgeAdj, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.one_apply]

/-- **The minority fence on the volume conductance bound**: the full
vertex set is not volume-minority (`2 · vol V ≤ vol V` fails since
`vol V = 2 > 0`), and the conclusion is refuted in proved form —
`φ · vol V = 2 ≤ boundary V = 0` is false on `K₂`. -/
theorem ichv_boundary_minority_fence_QA :
    ¬ (2 * vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2))
        ≤ vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2)))
      ∧ cheegerConstant cheegerEdgeAdj * vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2)) = 2
      ∧ boundary cheegerEdgeAdj (Finset.univ : Finset (Fin 2)) = 0 := by
  refine ⟨fun h => by
      rw [ichv_edge_vol_univ] at h
      norm_num at h, ?_, ?_⟩
  · rw [edge_cheegerConstant, ichv_edge_vol_univ]
    norm_num
  · simp [boundary]

/-- The signed fence fixture: symmetric, positive degrees (`1 = 2 - 1`),
nonnegative weights *fail* (entry `-1`). -/
def ichSigAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 2 else -1

theorem ichSigAdj_symmetric : ichSigAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [ichSigAdj]

theorem ichSigAdj_deg : ∀ i, deg ichSigAdj i = 1 := by
  intro i
  fin_cases i <;> simp [deg, ichSigAdj, Fin.sum_univ_two] <;> norm_num

theorem ichSigAdj_pos_deg : ∀ i, 0 < deg ichSigAdj i := by
  intro i
  rw [ichSigAdj_deg]
  norm_num

theorem ichSigAdj_not_nonneg : ¬ (∀ i j, 0 ≤ ichSigAdj i j) := by
  intro h
  have h1 := h 0 1
  simp [ichSigAdj] at h1
  linarith

/-- The signed fence's normalized Laplacian *is* `1 - ichSigAdj`
(the degrees are all `1`, so the degree scaling is trivial). -/
theorem ichSigAdj_normLap :
    normalizedLaplacian ichSigAdj = !![-1, 1; 1, -1] := by
  rw [normalizedLaplacian_eq_regularNormalizedLaplacian ichSigAdj 1
    ichSigAdj_deg (by norm_num), regularNormalizedLaplacian, inv_one,
    one_smul]
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.sub_apply, Matrix.one_apply, ichSigAdj, Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp <;> ring

/-- The signed fence's Cheeger constant is `-1`: both nonempty proper
cuts of `Fin 2` have conductance `boundary / vol = -1 / 1`. -/
theorem ichSigAdj_cheegerConstant : cheegerConstant ichSigAdj = -1 := by
  have hcond : ∀ i : Fin 2, conductance ichSigAdj {i} = -1 := by
    intro i
    have hvol1 : vol ichSigAdj {i} = 1 := by
      rw [vol, Finset.sum_singleton, ichSigAdj_deg]
    have hvol2 : vol ichSigAdj {i}ᶜ = 1 := by
      rw [vol, Finset.sum_congr rfl (fun _ _ => ichSigAdj_deg _),
        Finset.sum_const, Finset.card_compl, Finset.card_singleton,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num
    have hbd : boundary ichSigAdj {i} = -1 := by
      fin_cases i
      · simp [boundary, ichSigAdj,
          show ({0} : Finset (Fin 2))ᶜ = {1} by decide, Finset.sum_singleton]
      · simp [boundary, ichSigAdj,
          show ({1} : Finset (Fin 2))ᶜ = {0} by decide, Finset.sum_singleton]
    rw [conductance, hbd, hvol1, hvol2]
    norm_num
  have hset : {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance ichSigAdj S = c} = {-1} := by
    ext c
    constructor
    · rintro ⟨S, hne, hcn, rfl⟩
      fin_cases S
      · exact absurd hne (by decide)
      · exact hcond 0
      · exact hcond 1
      · exact absurd hcn (by decide)
    · rintro rfl
      exact ⟨{0}, by decide, by decide, hcond 0⟩
  rw [cheegerConstant, hset]
  simp

private theorem ich_sig_two_point_pin {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = -2)
    (hprod : l.prod = 0) : l.get ⟨1, by omega⟩ = 0 := by
  obtain ⟨a, b, hl⟩ : ∃ a b : ℝ, l = [a, b] := ⟨_, _, list_two_eq h2⟩
  subst hl
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  have hlt : (0 : Fin 2) < (1 : Fin 2) := by decide
  have hmono : a ≤ b := hs.rel_get_of_lt hlt
  rcases mul_eq_zero.1 hprod with h0 | h1
  · linarith
  · exact h1

/-- The signed fence's normalized Laplacian has sorted spectrum
`[-2, 0]` by the trace/determinant pin (trace `-2`, determinant `0`),
so `λ₂ = 0`. -/
theorem ichSigAdj_secondEval :
    secondEval (normalizedLaplacian ichSigAdj)
        (normalizedLaplacian_symmetric ichSigAdj ichSigAdj_symmetric)
        (le_refl 2) = 0 := by
  have hsymm' := normalizedLaplacian_symmetric ichSigAdj ichSigAdj_symmetric
  have htrace : (normalizedLaplacian ichSigAdj).trace = -2 := by
    rw [ichSigAdj_normLap]
    simp [Matrix.trace, Fin.sum_univ_two]
    norm_num
  have hdet : (normalizedLaplacian ichSigAdj).det = 0 := by
    rw [ichSigAdj_normLap, Matrix.det_fin_two_of]
    norm_num
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hsymm').eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hsymm').eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hsymm').eigenvalues))).sum = -2 := by
    have htr : ∑ i : Fin 2,
        eigvalOf (normalizedLaplacian ichSigAdj) hsymm' i = -2 := by
      rw [eigvalOf_sum_eq_trace, htrace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hsymm').eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2,
        ((isHermitian_of_isSymm hsymm').eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm hsymm').det_eq_prod_eigenvalues
      rw [hdet] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact ich_sig_two_point_pin hlen hsorted hsum hprod

/-- **The signed fence, refuted in proved form**: with every hypothesis
of `cheeger_lower_bound_normalized` except `hnn` verified on the signed
fixture (symmetry by entries, positive degrees `1 = 2 - 1`, two
vertices), the conclusion reads `φ²/2 = 1/2 ≤ λ₂ = 0` and is false —
the conductance side goes negative (`φ = -1`), squaring back above the
PSD-broken spectral side. Exactly the nonnegativity hypothesis is
isolated. -/
theorem ichv_signed_fence_QA :
    ¬ (cheegerConstant ichSigAdj ^ 2 / 2
        ≤ secondEval (normalizedLaplacian ichSigAdj)
          (normalizedLaplacian_symmetric ichSigAdj ichSigAdj_symmetric)
          (le_refl 2)) := by
  rw [ichSigAdj_cheegerConstant, ichSigAdj_secondEval]
  norm_num

/-!
## The connectivity transfer (QA)

QA for the connectivity-transfer family delivered 2026-08-26 in
`Scaffold.Mathlib.GraphTheory.VariationalTransfer`
(`proposals/irregular-cheeger-variational-transfer.md`, the priced
follow-on of the hard-direction delivery): the kernel characterization
`normalizedLaplacian_mulVec_eq_zero_iff`, the Fiedler mirror
`secondEval_normalizedLaplacian_pos_of_connected`, the disconnected
converse, the packaged iff, and the Cheeger consumer corollary
`cheegerConstant_pos_of_connected`. Sections: the P₃/K₂ positive
instances joined to the file's existing independent spectral pins; the
kernel iff exercised in both directions on genuinely irregular input;
the disconnected two-edge negative witness with `λ₂ = 0` pinned by two
independent routes; the `hconn` fence (proved form, every other
hypothesis verified); and the `hnn` fence on a *connected* signed
fixture — both at the kernel characterization and at the headline, the
latter through the engine with a fixture-specific squares PSD supplier
(the shelf's `normalizedLaplacian_psd` needs `hnn`; the engine does
not — the fence isolates exactly where nonnegativity enters).

Sections below this line are new (2026-08-26).
-/

/-- A nonzero vector has positive self dot product (local support
lemma, mirroring the module's private one). -/
private theorem dotProduct_pos_of_ne_zero' {V : Type} [Fintype V]
    {w : V → ℝ} (hw : w ≠ 0) : 0 < Matrix.dotProduct w w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw (funext hcon)
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

/-! ### P₃ connectivity + positive instance -/

theorem icP3_adj01 : (supportGraph icPathAdj icPathAdj_symmetric).Adj
    (0 : Fin 3) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [icPathAdj]⟩

theorem icP3_adj12 : (supportGraph icPathAdj icPathAdj_symmetric).Adj
    (1 : Fin 3) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [icPathAdj]⟩

theorem icP3_supportGraph_connected :
    (supportGraph icPathAdj icPathAdj_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons icP3_adj01 SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons icP3_adj01
      (SimpleGraph.Walk.cons icP3_adj12 SimpleGraph.Walk.nil)⟩

/-- The theorem's instance on the irregular fixture: `0 < λ₂ (L_sym P₃)`. -/
theorem icP3_secondEval_pos :
    0 < secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by norm_num) :=
  secondEval_normalizedLaplacian_pos_of_connected icPathAdj
    icPathAdj_symmetric icPathAdj_nonneg icPathAdj_pos_deg (by norm_num)
    icP3_supportGraph_connected

/-- The bracket joined to the independent eigenpair bound: `0 < λ₂ ≤ 1`
(the `≤ 1` side is the delivered eigenpair-witness pin, produced without
the connectivity theorem — non-circular). -/
theorem icP3_bracket :
    0 < secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by norm_num)
      ∧ secondEval (normalizedLaplacian icPathAdj)
          (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
          (by norm_num) ≤ 1 :=
  ⟨icP3_secondEval_pos, icPathAdj_secondEval_le_one⟩

/-! ### The kernel iff exercised on P₃ -/

/-- The degrees of the literal matrix, for entry computations after
`icPathAdj` is unfolded. -/
theorem icP3_deg_lit : ∀ i : Fin 3,
    deg !![0, 1, 0; 1, 0, 1; 0, 1, 0] i = if i = 1 then 2 else 1 := by
  intro i
  fin_cases i <;> simp [deg, Fin.sum_univ_three]
  all_goals norm_num

/-- Entry lemmas for the normalized Laplacian of `P₃` (the row-0
entries the kernel computation needs). -/
theorem icP3_normLap_00 :
    normalizedLaplacian icPathAdj 0 0 = 1 := by
  simp [normalizedLaplacian, icPathAdj, icP3_deg_lit, degreeInvSqrt,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply,
    Real.sqrt_one, sub_zero]

theorem icP3_normLap_01 :
    normalizedLaplacian icPathAdj 0 1 = -(Real.sqrt 2)⁻¹ := by
  simp [normalizedLaplacian, icPathAdj, icP3_deg_lit, degreeInvSqrt,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply,
    Real.sqrt_one, zero_sub]

theorem icP3_normLap_02 :
    normalizedLaplacian icPathAdj 0 2 = 0 := by
  simp [normalizedLaplacian, icPathAdj, icP3_deg_lit, degreeInvSqrt,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply,
    Real.sqrt_one, sub_self]

/-- The constants are NOT in the kernel on genuinely irregular input:
`L_sym P₃ *ᵥ onesVec ≠ 0` — entry `0` is `1 - (√2)⁻¹ ≠ 0`, computed
from per-entry lemmas. -/
theorem icP3_onesVec_not_kernel :
    normalizedLaplacian icPathAdj *ᵥ (onesVec : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_three,
    icP3_normLap_00, icP3_normLap_01, icP3_normLap_02, mul_one,
    Pi.zero_apply] at h0
  -- h0 : 1 + -(√2)⁻¹ + 0 = 0
  have hinv : (Real.sqrt 2 : ℝ)⁻¹ = 1 := by linarith
  rw [inv_eq_one] at hinv
  have h2 := icPathAdj_sqrt_two_sq
  rw [hinv] at h2
  norm_num at h2

/-- Through the iff: the constants are not spanned by `√D·1` on P₃. -/
theorem icP3_onesVec_not_span :
    ¬ ∃ c : ℝ, (onesVec : Fin 3 → ℝ)
      = c • (degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ)) := by
  intro h
  have hv := (normalizedLaplacian_mulVec_eq_zero_iff icPathAdj
    icPathAdj_symmetric icPathAdj_nonneg icPathAdj_pos_deg
    icP3_supportGraph_connected _).2 h
  exact icP3_onesVec_not_kernel hv

/-- The iff's forward direction on the pinned kernel vector: the
hypothesis (kernel membership) comes from the delivered shelf lemma at
the stretched constant, the conclusion identifies the line. -/
theorem icP3_kernelVec_span_raw :
    ∃ c : ℝ, (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      = c • (degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ)) := by
  refine (normalizedLaplacian_mulVec_eq_zero_iff icPathAdj
    icPathAdj_symmetric icPathAdj_nonneg icPathAdj_pos_deg
    icP3_supportGraph_connected _).1 ?_
  rw [← icPathAdj_kernelVec]
  exact normalizedLaplacian_mulVec_degreeSqrt_onesVec icPathAdj
    icPathAdj_pos_deg

/-- The span coefficient is forced: entry `0` pins `c = 1` (the
left-hand side's `1` against `c · √(deg 0) · 1 = c`). -/
theorem icP3_kernelVec_span_forced {c : ℝ}
    (hc : (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      = c • (degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ))) : c = 1 := by
  have h0 := congrFun hc 0
  simp only [Pi.smul_apply, smul_eq_mul, degreeSqrt_mulVec_apply,
    icPathAdj_deg, Real.sqrt_one, onesVec, mul_one, Matrix.cons_val_zero] at h0
  norm_num at h0
  exact h0.symm

/-! ### K₂ connectivity + join to the pinned λ₂ = 2 -/

theorem icK2_adj : (supportGraph cheegerEdgeAdj cheegerEdgeAdj_symmetric).Adj
    (0 : Fin 2) (1 : Fin 2) := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [cheegerEdgeAdj]⟩

theorem icK2_supportGraph_connected :
    (supportGraph cheegerEdgeAdj cheegerEdgeAdj_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons icK2_adj SimpleGraph.Walk.nil⟩

theorem icK2_secondEval_pos :
    0 < secondEval (normalizedLaplacian cheegerEdgeAdj)
        (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        (le_refl 2) :=
  secondEval_normalizedLaplacian_pos_of_connected cheegerEdgeAdj
    cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg icEdge_pos_deg (le_refl 2)
    icK2_supportGraph_connected

/-- The join: the theorem's positivity against the independently pinned
exact value `λ₂ = 2` (two constructions, one number). -/
theorem icK2_join :
    0 < secondEval (normalizedLaplacian cheegerEdgeAdj)
        (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        (le_refl 2)
      ∧ secondEval (normalizedLaplacian cheegerEdgeAdj)
          (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          (le_refl 2) = 2 :=
  ⟨icK2_secondEval_pos, icEdge_normLap_secondEval⟩

/-! ### The disconnected negative witness: two disjoint edges -/

/-- Two disjoint edges on `Fin 4` — symmetric, nonnegative, positive
degrees, but the support graph has two components. -/
def icDiscAdj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i ≠ j ∧ ((i : ℕ) ≤ 1) = ((j : ℕ) ≤ 1) then 1 else 0

theorem icDiscAdj_symmetric : icDiscAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [icDiscAdj]

theorem icDiscAdj_nonneg : ∀ i j, 0 ≤ icDiscAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [icDiscAdj, Matrix.of_apply]
  all_goals first | rfl | norm_num

theorem icDiscAdj_pos_deg : ∀ i, 0 < deg icDiscAdj i := by
  intro i
  have h01 : icDiscAdj 0 1 = 1 := by simp [icDiscAdj]
  have h10 : icDiscAdj 1 0 = 1 := by simp [icDiscAdj]
  have h23 : icDiscAdj 2 3 = 1 := by
    simp only [icDiscAdj, Matrix.of_apply, if_neg]
    rfl
  have h32 : icDiscAdj 3 2 = 1 := by
    simp only [icDiscAdj, Matrix.of_apply, if_neg]
    rfl
  fin_cases i
  · have h := Finset.single_le_sum (fun j _ => icDiscAdj_nonneg 0 j)
      (Finset.mem_univ 1)
    have hdeg : deg icDiscAdj 0 = ∑ j, icDiscAdj 0 j := rfl
    show (0 : ℝ) < deg icDiscAdj 0
    rw [hdeg]
    linarith
  · have h := Finset.single_le_sum (fun j _ => icDiscAdj_nonneg 1 j)
      (Finset.mem_univ 0)
    have hdeg : deg icDiscAdj 1 = ∑ j, icDiscAdj 1 j := rfl
    show (0 : ℝ) < deg icDiscAdj 1
    rw [hdeg]
    linarith
  · have h := Finset.single_le_sum (fun j _ => icDiscAdj_nonneg 2 j)
      (Finset.mem_univ 3)
    have hdeg : deg icDiscAdj 2 = ∑ j, icDiscAdj 2 j := rfl
    show (0 : ℝ) < deg icDiscAdj 2
    rw [hdeg]
    linarith
  · have h := Finset.single_le_sum (fun j _ => icDiscAdj_nonneg 3 j)
      (Finset.mem_univ 2)
    have hdeg : deg icDiscAdj 3 = ∑ j, icDiscAdj 3 j := rfl
    show (0 : ℝ) < deg icDiscAdj 3
    rw [hdeg]
    linarith

/-- Positive weights of the fixture never cross blocks. -/
theorem icDiscAdj_blocks (i j : Fin 4) (h : 0 < icDiscAdj i j) :
    decide ((i : ℕ) ≤ 1) = decide ((j : ℕ) ≤ 1) := by
  by_cases hsame : ((i : ℕ) ≤ 1) = ((j : ℕ) ≤ 1)
  · simp only [hsame]
  · exfalso
    have h0 : icDiscAdj i j = 0 := by
      simp only [icDiscAdj, Matrix.of_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, hsame]
    rw [h0] at h
    linarith

/-- Support-graph walks of the fixture never change block. -/
theorem icDisc_walk_blocks {u v : Fin 4}
    (w : (supportGraph icDiscAdj icDiscAdj_symmetric).Walk u v) :
    decide ((u : ℕ) ≤ 1) = decide ((v : ℕ) ≤ 1) := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    exact (icDiscAdj_blocks _ _ ((supportGraph_adj.1 hadj).2)).trans ih

/-- The support graph of the fixture is not connected: a walk from `0`
to `2` would have to change block. -/
theorem icDiscAdj_not_connected :
    ¬(supportGraph icDiscAdj icDiscAdj_symmetric).Connected := by
  intro hconn
  obtain ⟨w⟩ := hconn 0 2
  have hb := icDisc_walk_blocks w
  exact absurd hb (by decide)

/-- The block indicator `![1, 1, -1, -1]` is a combinatorial kernel
vector: positive weights never cross blocks, so every Laplacian row
annihilates it. -/
theorem icDisc_kernel_witness :
    (laplacian icDiscAdj) *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ) = 0 := by
  have hv : ∀ i j : Fin 4, 0 < icDiscAdj i j →
      (![1, 1, -1, -1] : Fin 4 → ℝ) i = (![1, 1, -1, -1] : Fin 4 → ℝ) j := by
    intro i j hij
    have hb := icDiscAdj_blocks i j hij
    have hval : ∀ k : Fin 4, (![1, 1, -1, -1] : Fin 4 → ℝ) k
        = if (k : ℕ) ≤ 1 then 1 else -1 := by
      intro k
      fin_cases k <;> rfl
    rw [hval i, hval j]
    by_cases hi : (i : ℕ) ≤ 1
    · have hj : (j : ℕ) ≤ 1 := by
        simpa [hi] using hb
      simp [hi, hj]
    · have hj : ¬((j : ℕ) ≤ 1) := by
        simpa [hi] using hb
      simp [hi, hj]
  funext i
  rw [laplacian_mulVec_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rcases eq_or_lt_of_le (icDiscAdj_nonneg i j) with h0 | hpos
  · rw [← h0, zero_mul]
  · rw [hv i j hpos, sub_self, mul_zero]

/-- **The theorem's route**: disconnected ⇒ `λ₂ = 0`. -/
theorem icDisc_secondEval_eq_zero :
    secondEval (normalizedLaplacian icDiscAdj)
        (normalizedLaplacian_symmetric icDiscAdj icDiscAdj_symmetric)
        (by norm_num) = 0 :=
  secondEval_normalizedLaplacian_eq_zero_of_not_connected icDiscAdj
    icDiscAdj_symmetric icDiscAdj_nonneg icDiscAdj_pos_deg (by norm_num)
    icDiscAdj_not_connected

/-- **The independent route**: the engine + the raw kernel witness give
`λ₂ ≤ 0` with no connectivity theorem anywhere. The test vector is the
Gram–Schmidt combination of the two stretched kernel vectors. -/
theorem icDisc_secondEval_le_zero :
    secondEval (normalizedLaplacian icDiscAdj)
        (normalizedLaplacian_symmetric icDiscAdj icDiscAdj_symmetric)
        (by norm_num) ≤ 0 := by
  have hwne : degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    rw [degreeSqrt_mulVec_apply] at h1
    simp only [onesVec, mul_one] at h1
    exact (Real.sqrt_ne_zero'.2 (icDiscAdj_pos_deg 1)) h1
  have hwker : normalizedLaplacian icDiscAdj *ᵥ
      (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)) = 0 :=
    normalizedLaplacian_mulVec_degreeSqrt_onesVec icDiscAdj icDiscAdj_pos_deg
  have hgker : normalizedLaplacian icDiscAdj *ᵥ
      (degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ)) = 0 :=
    normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero
      icDiscAdj icDiscAdj_pos_deg icDisc_kernel_witness
  have hwwpos : 0 < Matrix.dotProduct
      (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
      (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)) :=
    dotProduct_pos_of_ne_zero' hwne
  set c : ℝ := Matrix.dotProduct
      (degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ))
      (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
    * (Matrix.dotProduct (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
      (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)))⁻¹ with hc
  set x : Fin 4 → ℝ := degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ)
    - c • (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)) with hx
  have hxorth : Matrix.dotProduct x
      (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)) = 0 := by
    have hcomm : Matrix.dotProduct
        (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
        (degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ))
        = Matrix.dotProduct
          (degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ))
          (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)) :=
      Matrix.dotProduct_comm _ _
    have hcancel : Matrix.dotProduct
          (degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ))
          (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
        * (Matrix.dotProduct (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
          (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)))⁻¹
        * Matrix.dotProduct (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
          (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
      = Matrix.dotProduct
          (degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ))
        (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)) := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hwwpos), mul_one]
    rw [hx, Matrix.dotProduct_comm, Matrix.dotProduct_sub,
      Matrix.dotProduct_smul, hcomm, smul_eq_mul, hc, hcancel]
    ring
  have hxker : normalizedLaplacian icDiscAdj *ᵥ x = 0 := by
    rw [hx, Matrix.mulVec_sub, Matrix.mulVec_smul, hgker, hwker, smul_zero,
      sub_zero]
  have hxne : x ≠ 0 := by
    intro hx0
    rw [hx] at hx0
    have hsub : degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ)
        = c • (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)) :=
      sub_eq_zero.1 hx0
    have hcancel : degreeInvSqrt icDiscAdj *ᵥ
        (degreeSqrt icDiscAdj *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ))
      = (![1, 1, -1, -1] : Fin 4 → ℝ) := by
      rw [Matrix.mulVec_mulVec, degreeInvSqrt_mul_degreeSqrt icDiscAdj
        icDiscAdj_pos_deg, Matrix.one_mulVec]
    have hcancelw : degreeInvSqrt icDiscAdj *ᵥ
        (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
      = (onesVec : Fin 4 → ℝ) := by
      rw [Matrix.mulVec_mulVec, degreeInvSqrt_mul_degreeSqrt icDiscAdj
        icDiscAdj_pos_deg, Matrix.one_mulVec]
    have hun : (![1, 1, -1, -1] : Fin 4 → ℝ)
        = c • (onesVec : Fin 4 → ℝ) := by
      rw [← hcancel, hsub, Matrix.mulVec_smul_assoc, hcancelw]
    have h0 : (1 : ℝ) = c := by
      have hq := congrFun hun 0
      simp only [Pi.smul_apply, smul_eq_mul, onesVec, mul_one,
        Matrix.cons_val_zero] at hq
      exact hq
    have h2 : (-1 : ℝ) = c := by
      have hq := congrFun hun 2
      simp only [Pi.smul_apply, smul_eq_mul, onesVec, mul_one,
        Matrix.cons_val_succ, Matrix.head_cons] at hq
      exact hq
    linarith
  have hle := secondEval_le_rayleigh_of_ker
    (normalizedLaplacian_symmetric icDiscAdj icDiscAdj_symmetric)
    (normalizedLaplacian_psd icDiscAdj icDiscAdj_symmetric icDiscAdj_nonneg
      icDiscAdj_pos_deg)
    hwne hwker (by norm_num) hxne hxorth
  have hray : rayleigh (normalizedLaplacian icDiscAdj) x = 0 := by
    rw [rayleigh, if_neg hxne, div_eq_zero_iff]
    exact Or.inl (by rw [quadForm, hxker, Matrix.dotProduct_zero])
  exact hle.trans_eq hray

/-- **Two routes, one number**: the theorem gives `λ₂ = 0`; the raw
kernel witness + engine give `λ₂ ≤ 0` independently of any connectivity
statement. -/
theorem icDisc_two_routes :
    secondEval (normalizedLaplacian icDiscAdj)
        (normalizedLaplacian_symmetric icDiscAdj icDiscAdj_symmetric)
        (by norm_num) = 0
      ∧ secondEval (normalizedLaplacian icDiscAdj)
          (normalizedLaplacian_symmetric icDiscAdj icDiscAdj_symmetric)
          (by norm_num) ≤ 0 :=
  ⟨icDisc_secondEval_eq_zero, icDisc_secondEval_le_zero⟩

/-- **The connectivity fence, proved form**: every hypothesis of
`secondEval_normalizedLaplacian_pos_of_connected` except `hconn` holds
on the fixture, and the conclusion is refuted — exactly `hconn`
isolated. -/
theorem icDisc_hconn_fence :
    icDiscAdj.IsSymm
      ∧ (∀ i j, 0 ≤ icDiscAdj i j)
      ∧ (∀ i, 0 < deg icDiscAdj i)
      ∧ 2 ≤ Fintype.card (Fin 4)
      ∧ ¬(supportGraph icDiscAdj icDiscAdj_symmetric).Connected
      ∧ ¬(0 < secondEval (normalizedLaplacian icDiscAdj)
            (normalizedLaplacian_symmetric icDiscAdj icDiscAdj_symmetric)
            (by norm_num)) :=
  ⟨icDiscAdj_symmetric, icDiscAdj_nonneg, icDiscAdj_pos_deg, by norm_num,
    icDiscAdj_not_connected, by
      rw [icDisc_secondEval_eq_zero]
      norm_num⟩

/-! ### The signed connected fence (`hnn` isolated) -/

/-- A connected, positive-degree, *signed* fixture: the support edges
`0—1`, `0—2` are positive, but `A 1 2 = -1`. -/
def icSigConnAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if ((i : ℕ) = 0 ∧ (j : ℕ) ≠ 0) ∨ ((j : ℕ) = 0 ∧ (i : ℕ) ≠ 0) then 2
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 2 ∨ (i : ℕ) = 2 ∧ (j : ℕ) = 1 then -1
    else 0

theorem icSigConnAdj_symmetric : icSigConnAdj.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [icSigConnAdj]

theorem icSigConnAdj_not_nonneg :
    ¬ (∀ i j, 0 ≤ icSigConnAdj i j) := by
  intro h
  have h1 := h 1 2
  simp only [icSigConnAdj] at h1
  norm_num at h1

theorem icSigConnAdj_deg :
    ∀ i, deg icSigConnAdj i = if i = 0 then 4 else 1 := by
  intro i
  fin_cases i <;> simp [deg, icSigConnAdj, Fin.sum_univ_three] <;> norm_num

theorem icSigConnAdj_pos_deg : ∀ i, 0 < deg icSigConnAdj i := by
  intro i
  fin_cases i <;> simp [icSigConnAdj_deg]

theorem icSigConn_adj01 :
    (supportGraph icSigConnAdj icSigConnAdj_symmetric).Adj (0 : Fin 3) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [icSigConnAdj]⟩

theorem icSigConn_adj02 :
    (supportGraph icSigConnAdj icSigConnAdj_symmetric).Adj (0 : Fin 3) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [icSigConnAdj]⟩

theorem icSigConn_connected :
    (supportGraph icSigConnAdj icSigConnAdj_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons icSigConn_adj01 SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons icSigConn_adj02 SimpleGraph.Walk.nil⟩

/-- The entry form of the signed fixture's normalized Laplacian (the
`√4 = 2` scaling making every entry rational). -/
theorem icSigConn_normLap_entry (i j : Fin 3) :
    normalizedLaplacian icSigConnAdj i j
      = (if i = j then (1 : ℝ) else 0)
        - (Real.sqrt (deg icSigConnAdj i))⁻¹ * icSigConnAdj i j
          * (Real.sqrt (deg icSigConnAdj j))⁻¹ := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply]

/-- The closed entry form of the signed fixture's normalized Laplacian:
diagonal `1`, the `(1,2)`/`(2,1)` pair `+1` (the negative weight), all
other off-diagonal entries `-1`. -/
theorem icSigConnAdj_normLap (i j : Fin 3) :
    normalizedLaplacian icSigConnAdj i j
      = if i = j then (1 : ℝ)
        else if (i : ℕ) = 1 ∧ (j : ℕ) = 2 ∨ (i : ℕ) = 2 ∧ (j : ℕ) = 1
          then 1 else -1 := by
  have hs4 : (Real.sqrt 4 : ℝ) = 2 := by
    have hnn := Real.sqrt_nonneg 4
    have hsq := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have hA : ∀ i j : Fin 3, icSigConnAdj i j =
      (if ((i : ℕ) = 0 ∧ (j : ℕ) ≠ 0) ∨ ((j : ℕ) = 0 ∧ (i : ℕ) ≠ 0) then 2
      else if (i : ℕ) = 1 ∧ (j : ℕ) = 2 ∨ (i : ℕ) = 2 ∧ (j : ℕ) = 1 then -1
      else 0) := fun i j => rfl
  rw [icSigConn_normLap_entry, hA]
  fin_cases i <;> fin_cases j <;>
    simp [icSigConnAdj_deg, hs4, Real.sqrt_one]

/-- The non-stretched kernel vector `![0, 1, -1]`, raw: verified
entrywise against the closed entry form. -/
theorem icSigConn_kernel_witness :
    normalizedLaplacian icSigConnAdj *ᵥ (![0, 1, -1] : Fin 3 → ℝ) = 0 := by
  funext i
  fin_cases i <;>
    simp [icSigConnAdj_normLap, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_three]

theorem icSigConn_witness_ne : (![0, 1, -1] : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp at h1

theorem icSigConn_stretchVec :
    degreeSqrt icSigConnAdj *ᵥ (onesVec : Fin 3 → ℝ) = ![2, 1, 1] := by
  have hs4 : (Real.sqrt 4 : ℝ) = 2 := by
    have hnn := Real.sqrt_nonneg 4
    have hsq := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  funext i
  rw [degreeSqrt_mulVec_apply, icSigConnAdj_deg, onesVec, mul_one]
  fin_cases i <;> simp [hs4, Real.sqrt_one]

theorem icSigConn_w_kernel :
    normalizedLaplacian icSigConnAdj *ᵥ
      (degreeSqrt icSigConnAdj *ᵥ (onesVec : Fin 3 → ℝ)) = 0 :=
  normalizedLaplacian_mulVec_degreeSqrt_onesVec icSigConnAdj
    icSigConnAdj_pos_deg

theorem icSigConn_w_ne :
    degreeSqrt icSigConnAdj *ᵥ (onesVec : Fin 3 → ℝ) ≠ 0 := by
  rw [icSigConn_stretchVec]
  intro h
  have h0 := congrFun h 0
  simp at h0

theorem icSigConn_witness_orth :
    Matrix.dotProduct (![0, 1, -1] : Fin 3 → ℝ)
      (degreeSqrt icSigConnAdj *ᵥ (onesVec : Fin 3 → ℝ)) = 0 := by
  rw [icSigConn_stretchVec]
  simp only [Matrix.dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons]
  norm_num

/-- **The kernel-characterization fence, proved form**: on this
connected fixture the kernel contains `![0, 1, -1]`, but that vector is
not a multiple of `√D·1 = ![2, 1, 1]` — so the characterization's
conclusion fails while every hypothesis except `hnn` holds. Exactly
`hnn` isolated, at the entry the proposal names. -/
theorem icSigConn_kernel_fence :
    icSigConnAdj.IsSymm
      ∧ (∀ i, 0 < deg icSigConnAdj i)
      ∧ 2 ≤ Fintype.card (Fin 3)
      ∧ (supportGraph icSigConnAdj icSigConnAdj_symmetric).Connected
      ∧ normalizedLaplacian icSigConnAdj *ᵥ (![0, 1, -1] : Fin 3 → ℝ) = 0
      ∧ ¬(∃ c : ℝ, (![0, 1, -1] : Fin 3 → ℝ)
            = c • (degreeSqrt icSigConnAdj *ᵥ (onesVec : Fin 3 → ℝ))) :=
  ⟨icSigConnAdj_symmetric, icSigConnAdj_pos_deg, by norm_num,
    icSigConn_connected, icSigConn_kernel_witness, by
      rintro ⟨c, hc⟩
      rw [icSigConn_stretchVec] at hc
      have h0 := congrFun hc 0
      have h1 := congrFun hc 1
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] at h0 h1
      norm_num at h0 h1
      linarith⟩

/-- The fixture's PSD supplier, proved by the squares identity
`(x 0 - x 1 - x 2)²` — this is where `hnn` enters the engine route:
the shelf's `normalizedLaplacian_psd` needs nonnegativity, the fixture
does not. -/
theorem icSigConn_psd :
    ∀ x : Fin 3 → ℝ, 0 ≤ quadForm (normalizedLaplacian icSigConnAdj) x := by
  intro x
  have hexp : quadForm (normalizedLaplacian icSigConnAdj) x
      = (x 0 - x 1 - x 2) ^ 2 := by
    rw [quadForm]
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      icSigConnAdj_normLap]
    simp
    ring
  rw [hexp]
  exact sq_nonneg _

/-- **The headline fence, proved form**: every hypothesis of the
positivity theorem except `hnn` holds — including connectivity — and
the conclusion is refuted (`λ₂ ≤ 0` through the engine at the raw
orthogonal kernel witness, PSD supplied by the squares identity). -/
theorem icSigConn_fence :
    icSigConnAdj.IsSymm
      ∧ (∀ i, 0 < deg icSigConnAdj i)
      ∧ 2 ≤ Fintype.card (Fin 3)
      ∧ (supportGraph icSigConnAdj icSigConnAdj_symmetric).Connected
      ∧ ¬(0 < secondEval (normalizedLaplacian icSigConnAdj)
            (normalizedLaplacian_symmetric icSigConnAdj
              icSigConnAdj_symmetric)
            (by norm_num)) := by
  refine ⟨icSigConnAdj_symmetric, icSigConnAdj_pos_deg, by norm_num,
    icSigConn_connected, ?_⟩
  intro hpos
  have hle := secondEval_le_rayleigh_of_ker
    (normalizedLaplacian_symmetric icSigConnAdj icSigConnAdj_symmetric)
    icSigConn_psd icSigConn_w_ne icSigConn_w_kernel (by norm_num)
    icSigConn_witness_ne icSigConn_witness_orth
  have hray : rayleigh (normalizedLaplacian icSigConnAdj)
      (![0, 1, -1] : Fin 3 → ℝ) = 0 := by
    rw [rayleigh, if_neg icSigConn_witness_ne, div_eq_zero_iff]
    refine Or.inl ?_
    rw [quadForm, icSigConn_kernel_witness, Matrix.dotProduct_zero]
  rw [hray] at hle
  linarith

/-! ### The Cheeger consumer corollary, instantiated -/

/-- The corollary on the irregular fixture, against the pinned
`cheegerConstant = 1` (two routes, one number). -/
theorem icP3_cheegerConstant_pos :
    0 < cheegerConstant icPathAdj :=
  cheegerConstant_pos_of_connected icPathAdj icPathAdj_symmetric
    icPathAdj_nonneg icPathAdj_pos_deg (by norm_num)
    icP3_supportGraph_connected

theorem icP3_cheegerConstant_join :
    0 < cheegerConstant icPathAdj ∧ cheegerConstant icPathAdj = 1 :=
  ⟨icP3_cheegerConstant_pos, icPathAdj_cheegerConstant⟩

theorem icK2_cheegerConstant_pos :
    0 < cheegerConstant cheegerEdgeAdj :=
  cheegerConstant_pos_of_connected cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg
    icEdge_pos_deg (by norm_num) icK2_supportGraph_connected

theorem icK2_cheegerConstant_join :
    0 < cheegerConstant cheegerEdgeAdj ∧ cheegerConstant cheegerEdgeAdj = 1 :=
  ⟨icK2_cheegerConstant_pos, edge_cheegerConstant⟩

/-!
### The volume-weighted sweep-cut extraction QA (2026-08-26)

The irregular family's sweep extraction — the per-part
`sweep_level_extract_vol` and the median assembly
`cheeger_sweep_cut_normalized` — exercised at three levels: the
extraction witness *forced* on genuinely irregular input (the level
membership iff pins the returned set), the sweep-cut joined to the
file's independently pinned Rayleigh values on the pair's shared cut
test vector and on the `K₂` regular cone, and the degree-weighted
zero-sum fence refuting the hypothesis-dropped conclusion in proved
form.
-/

/-- The extraction test function on `P₃`: a single positive value at
the irregular vertex, `y = ![1, 0, 0]` (degrees `1, 2, 1`). -/
def vscY : Fin 3 → ℝ := ![1, 0, 0]

theorem vscY_sq (i : Fin 3) : vscY i ^ 2 = if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [vscY]

theorem vscY_minority : ∀ t : ℝ, 0 < t →
    2 * vol icPathAdj (Finset.univ.filter (fun i => t ≤ vscY i ^ 2))
      ≤ vol icPathAdj (Finset.univ : Finset (Fin 3)) := by
  intro t ht
  have hsub : (Finset.univ.filter (fun i => t ≤ vscY i ^ 2))
      ⊆ ({0} : Finset (Fin 3)) := by
    intro i hi
    by_cases h0 : i = 0
    · simp [h0]
    · exfalso
      have hc := (Finset.mem_filter.1 hi).2
      rw [vscY_sq i, if_neg h0] at hc
      linarith
  have h1 := vol_le_vol_of_subset icPathAdj icPathAdj_nonneg hsub
  rw [icPathAdj_vol_zero] at h1
  rw [icPathAdj_vol_univ]
  linarith

theorem vscY_M : ∑ i, deg icPathAdj i * vscY i ^ 2 = 1 := by
  simp [Fin.sum_univ_three, deg, icPathAdj, vscY]

theorem vscY_E :
    ∑ i, ∑ j, icPathAdj i j * (vscY i - vscY j) ^ 2 = 2 := by
  simp [Fin.sum_univ_three, icPathAdj, vscY]
  norm_num

/-- **The per-part extraction forced on `P₃`**: at `y = ![1, 0, 0]` the
level membership iff *forces* the extracted set — the filter is a
subset of `{0}` (the sole positive value), and nonemptiness rules out
`∅`, so the returned cut is pinned, its conductance computed to `1`
raw (the file's exhaustive-cut pin), and the theorem bound reads
`1 ≤ 2 / 1` with both sides computed raw. -/
theorem vsc_extract_p3_QA :
    ∃ S : Finset (Fin 3), ∃ t : ℝ, 0 < t ∧ (∀ i, i ∈ S ↔ t ≤ vscY i ^ 2) ∧
      S = ({0} : Finset (Fin 3)) ∧
      conductance icPathAdj S = 1 ∧
      conductance icPathAdj S ^ 2
        ≤ (∑ i, ∑ j, icPathAdj i j * (vscY i - vscY j) ^ 2)
          / (∑ i, deg icPathAdj i * vscY i ^ 2)
      ∧ (∑ i, ∑ j, icPathAdj i j * (vscY i - vscY j) ^ 2) = 2
      ∧ (∑ i, deg icPathAdj i * vscY i ^ 2) = 1 := by
  obtain ⟨S, t, ht, hSmem, hSne, hScne, hle⟩ :=
    sweep_level_extract_vol icPathAdj icPathAdj_symmetric icPathAdj_nonneg
      icPathAdj_pos_deg vscY vscY_minority (by rw [vscY_M]; norm_num)
  have hsub : ∀ i ∈ S, i = (0 : Fin 3) := by
    intro i hi
    have hci := (hSmem i).1 hi
    rw [vscY_sq i] at hci
    by_cases h0 : i = 0
    · exact h0
    · exfalso
      rw [if_neg h0] at hci
      linarith
  obtain ⟨iS, hiS⟩ := hSne
  have h0S : (0 : Fin 3) ∈ S := by
    have hi0 : iS = (0 : Fin 3) := hsub iS hiS
    rw [← hi0]
    exact hiS
  have hSetEq : S = ({0} : Finset (Fin 3)) := by
    refine Finset.ext fun i => ?_
    constructor
    · intro hi
      exact Finset.mem_singleton.2 (hsub i hi)
    · intro hi
      have hi0 : i = (0 : Fin 3) := Finset.mem_singleton.1 hi
      rw [hi0]
      exact h0S
  refine ⟨S, t, ht, hSmem, hSetEq, ?_, ?_, vscY_E, vscY_M⟩
  · rw [hSetEq]; exact ic_cond_0
  · rw [hSetEq, ic_cond_0, vscY_E, vscY_M]
    norm_num

/-- The `K₂` singleton conductance, from the reused boundary/volume
pins (the derivation `edge_cheegerConstant` internalizes, exposed for
the sweep-cut instances below). -/
theorem vsc_edge_cond_singleton (i : Fin 2) :
    conductance cheegerEdgeAdj ({i} : Finset (Fin 2)) = 1 := by
  obtain ⟨hv1, hv2⟩ := edge_vol_singleton i
  rw [conductance, edge_boundary_singleton i, hv1, hv2]
  norm_num

/-- The three-case split on `Fin 3` (the pin's
`Fin.exists_eq_zero_or_eq_one_or_eq_two` is absent; a local clone). -/
theorem vsc_fin3_cases (i : Fin 3) :
    i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

/-- **The sweep-cut on `P₃`'s shared cut test vector** — the same
object both directions of the Cheeger pair consume
(`cutTestVector icPathAdj {0} = ![3, -1, -1]`, degree-weighted zero
sum by the delivered lemma): the returned set lies in the two-member
sweep family (`{0}` superlevel, `{1, 2}` sublevel — the family
characterization is proved in-instance), hence has conductance exactly
`1` (the exhaustive-cut pin), and the theorem bound reads
`1 ≤ 2 · 4/3` against the file's pinned Rayleigh value. -/
theorem vsc_cut_p3_QA :
    ∃ S : Finset (Fin 3), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ cutTestVector icPathAdj
            ({0} : Finset (Fin 3)) i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ cutTestVector icPathAdj
            ({0} : Finset (Fin 3)) i ≤ t)) ∧
      conductance icPathAdj S = 1 ∧
      conductance icPathAdj S ^ 2
        ≤ 2 * rayleigh (normalizedLaplacian icPathAdj)
            (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj
              ({0} : Finset (Fin 3)))
      ∧ 2 * rayleigh (normalizedLaplacian icPathAdj)
            (degreeSqrt icPathAdj *ᵥ cutTestVector icPathAdj
              ({0} : Finset (Fin 3))) = 8 / 3 := by
  have hcvne : cutTestVector icPathAdj ({0} : Finset (Fin 3)) ≠ 0 := by
    intro h
    have h0 : cutTestVector icPathAdj ({0} : Finset (Fin 3)) 0 = 0 :=
      congrFun h 0
    rw [icPathAdj_cutVec] at h0
    simp at h0
  obtain ⟨S, hSne, hSc, hfam, hle⟩ :=
    cheeger_sweep_cut_normalized icPathAdj icPathAdj_symmetric
      icPathAdj_nonneg icPathAdj_pos_deg hcvne ichv_cutVec_weighted_sum
  have hf0 : cutTestVector icPathAdj ({0} : Finset (Fin 3)) 0 = 3 := by
    rw [icPathAdj_cutVec]; simp
  have hf1 : cutTestVector icPathAdj ({0} : Finset (Fin 3)) 1 = -1 := by
    rw [icPathAdj_cutVec]; simp
  have hf2 : cutTestVector icPathAdj ({0} : Finset (Fin 3)) 2 = -1 := by
    rw [icPathAdj_cutVec]; simp
  rcases hfam with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- superlevel: the negative values cannot enter without the whole set
    have h1n : (1 : Fin 3) ∉ S := by
      intro h1
      have hc1 := (ht 1).1 h1
      rw [hf1] at hc1
      have h0 : (0 : Fin 3) ∈ S := (ht 0).2 (by rw [hf0]; linarith)
      have h2 : (2 : Fin 3) ∈ S := (ht 2).2 (by rw [hf2]; linarith)
      have hU : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · simpa using h0
        · simpa using h1
        · simpa using h2)
      rw [hU] at hSc
      simp at hSc
    have h2n : (2 : Fin 3) ∉ S := by
      intro h2
      have hc2 := (ht 2).1 h2
      rw [hf2] at hc2
      have h0 : (0 : Fin 3) ∈ S := (ht 0).2 (by rw [hf0]; linarith)
      have h1 : (1 : Fin 3) ∈ S := (ht 1).2 (by rw [hf1]; linarith)
      have hU : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · simpa using h0
        · simpa using h1
        · simpa using h2)
      rw [hU] at hSc
      simp at hSc
    obtain ⟨iS, hiS⟩ := hSne
    have h0S : (0 : Fin 3) ∈ S := by
      rcases vsc_fin3_cases iS with h | h | h
      · exact h ▸ hiS
      · rw [h] at hiS; exact absurd hiS h1n
      · rw [h] at hiS; exact absurd hiS h2n
    have hSetEq : S = ({0} : Finset (Fin 3)) := by
      refine Finset.ext fun i => ?_
      constructor
      · intro hi
        have : i = (0 : Fin 3) := by
          rcases vsc_fin3_cases i with h | h | h
          · exact h
          · rw [h] at hi; exact absurd hi h1n
          · rw [h] at hi; exact absurd hi h2n
        exact Finset.mem_singleton.2 this
      · intro hi
        have hi0 : i = (0 : Fin 3) := Finset.mem_singleton.1 hi
        rw [hi0]
        exact h0S
    exact ⟨S, ⟨iS, hiS⟩, hSc, Or.inl ⟨t, ht⟩,
      by rw [hSetEq]; exact ic_cond_0,
      by rw [hSetEq, ic_cond_0, icPathAdj_rayleigh]; norm_num,
      by rw [icPathAdj_rayleigh]; norm_num⟩
  · -- sublevel: the top value cannot enter without the whole set
    have h0n : (0 : Fin 3) ∉ S := by
      intro h0
      have hc0 := (ht 0).1 h0
      rw [hf0] at hc0
      have h1 : (1 : Fin 3) ∈ S := (ht 1).2 (by rw [hf1]; linarith)
      have h2 : (2 : Fin 3) ∈ S := (ht 2).2 (by rw [hf2]; linarith)
      have hU : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · simpa using h0
        · simpa using h1
        · simpa using h2)
      rw [hU] at hSc
      simp at hSc
    have h1S : (1 : Fin 3) ∈ S := by
      obtain ⟨iS, hiS⟩ := hSne
      rcases vsc_fin3_cases iS with h | h | h
      · rw [h] at hiS; exact absurd hiS h0n
      · exact h ▸ hiS
      · rw [h] at hiS
        have hc2 := (ht 2).1 hiS
        rw [hf2] at hc2
        exact (ht 1).2 (by rw [hf1]; linarith)
    have h2S : (2 : Fin 3) ∈ S := by
      have hc1 := (ht 1).1 h1S
      rw [hf1] at hc1
      exact (ht 2).2 (by rw [hf2]; linarith)
    have hSetEq : S = ({1, 2} : Finset (Fin 3)) := by
      refine Finset.ext fun i => ?_
      constructor
      · intro hi
        rcases vsc_fin3_cases i with h | h | h
        · rw [h] at hi; exact absurd hi h0n
        · rw [h]; decide
        · rw [h]; decide
      · intro hi
        rcases vsc_fin3_cases i with h | h | h
        · rw [h] at hi; exact absurd hi (by simp)
        · rw [h]; simpa using h1S
        · rw [h]; simpa using h2S
    refine ⟨S, hSne, hSc, Or.inr ⟨t, ht⟩, ?_, ?_, ?_⟩
    · rw [hSetEq]; exact ic_cond_12
    · rw [hSetEq, ic_cond_12, icPathAdj_rayleigh]; norm_num
    · rw [icPathAdj_rayleigh]; norm_num

/-- **The sweep-cut regular recovery on `K₂`**: at `f = ![1, -1]`
(degree-weighted zero sum, all degrees `1`), the returned set lies in
the two-member family (`{0}` superlevel, `{1}` sublevel), hence has
conductance exactly `1`, and the theorem bound reads `1 ≤ 2 · 2 = 4`
against the pinned Rayleigh value `2` — the same number the regular
family's own sweep QA reaches. -/
theorem vsc_cut_edge_QA :
    ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ (![1, -1] : Fin 2 → ℝ) i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ (![1, -1] : Fin 2 → ℝ) i ≤ t)) ∧
      conductance cheegerEdgeAdj S = 1 ∧
      conductance cheegerEdgeAdj S ^ 2
        ≤ 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))
      ∧ 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)) = 4 := by
  have hne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, -1] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have horth : ∑ i, deg cheegerEdgeAdj i * (![1, -1] : Fin 2 → ℝ) i = 0 := by
    rw [Fin.sum_univ_two, cheegerEdgeAdj_regular 0, cheegerEdgeAdj_regular 1]
    norm_num
  obtain ⟨S, hSne, hSc, hfam, hle⟩ :=
    cheeger_sweep_cut_normalized cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg
      ichv_edge_pos_deg hne horth
  have hf0 : (![1, -1] : Fin 2 → ℝ) 0 = 1 := by simp
  have hf1 : (![1, -1] : Fin 2 → ℝ) 1 = -1 := by simp
  rcases hfam with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- superlevel: the low value cannot enter without the whole set
    have h1n : (1 : Fin 2) ∉ S := by
      intro h1
      have hc1 := (ht 1).1 h1
      rw [hf1] at hc1
      have h0 : (0 : Fin 2) ∈ S := (ht 0).2 (by rw [hf0]; linarith)
      have hU : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · simpa using h0
        · simpa using h1)
      rw [hU] at hSc
      simp at hSc
    obtain ⟨iS, hiS⟩ := hSne
    have h0S : (0 : Fin 2) ∈ S := by
      fin_cases iS
      · exact hiS
      · exact absurd hiS h1n
    have hSetEq : S = ({0} : Finset (Fin 2)) := by
      refine Finset.ext fun i => ?_
      constructor
      · intro hi
        fin_cases i
        · simp
        · exact absurd hi h1n
      · intro hi
        have hi0 : i = (0 : Fin 2) := Finset.mem_singleton.1 hi
        rw [hi0]
        exact h0S
    have hb1 : conductance cheegerEdgeAdj S ^ 2
        ≤ 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)) := by
      rw [hSetEq, vsc_edge_cond_singleton 0, (ichv_sweep_edge_QA).2]
      norm_num
    have hb2 : 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
        (degreeSqrt cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)) = 4 := by
      rw [(ichv_sweep_edge_QA).2]
      norm_num
    exact ⟨S, ⟨iS, hiS⟩, hSc, Or.inl ⟨t, ht⟩,
      by rw [hSetEq]; exact vsc_edge_cond_singleton 0, hb1, hb2⟩
  · -- sublevel: the top value cannot enter without the whole set
    have h0n : (0 : Fin 2) ∉ S := by
      intro h0
      have hc0 := (ht 0).1 h0
      rw [hf0] at hc0
      have h1 : (1 : Fin 2) ∈ S := (ht 1).2 (by rw [hf1]; linarith)
      have hU : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · simpa using h0
        · simpa using h1)
      rw [hU] at hSc
      simp at hSc
    obtain ⟨iS, hiS⟩ := hSne
    have h1S : (1 : Fin 2) ∈ S := by
      fin_cases iS
      · exact absurd hiS h0n
      · exact hiS
    have hSetEq : S = ({1} : Finset (Fin 2)) := by
      refine Finset.ext fun i => ?_
      constructor
      · intro hi
        fin_cases i
        · exact absurd hi h0n
        · simp
      · intro hi
        have hi1 : i = (1 : Fin 2) := Finset.mem_singleton.1 hi
        rw [hi1]
        exact h1S
    have hb1 : conductance cheegerEdgeAdj S ^ 2
        ≤ 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)) := by
      rw [hSetEq, vsc_edge_cond_singleton 1, (ichv_sweep_edge_QA).2]
      norm_num
    have hb2 : 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
        (degreeSqrt cheegerEdgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ)) = 4 := by
      rw [(ichv_sweep_edge_QA).2]
      norm_num
    exact ⟨S, ⟨iS, hiS⟩, hSc, Or.inr ⟨t, ht⟩,
      by rw [hSetEq]; exact vsc_edge_cond_singleton 1, hb1, hb2⟩

/-- **The degree-weighted zero-sum fence (proved refutation).** At
`f = ![1, 2]` on `K₂` the hypothesis `∑ deg · f = 3 ≠ 0` fails, and the
hypothesis-free conclusion is false for *every* candidate: the sweep
family of `![1, 2]` has exactly two nonempty proper members (`{0}` and
`{1}`), each of conductance `1`, while the demanded bound is
`1 ≤ 2 · R = 2/5` (`R = 1/5` computed raw: Dirichlet energy `1`,
squared norm `5`). Exactly `horth` isolated. -/
theorem vsc_cut_orth_dropped_refuted_QA :
    ¬ (∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ (![1, 2] : Fin 2 → ℝ) i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ (![1, 2] : Fin 2 → ℝ) i ≤ t)) ∧
      conductance cheegerEdgeAdj S ^ 2
        ≤ 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (![1, 2] : Fin 2 → ℝ)))
      ∧ ∑ i, deg cheegerEdgeAdj i * (![1, 2] : Fin 2 → ℝ) i = 3
      ∧ 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (![1, 2] : Fin 2 → ℝ)) = 2 / 5 := by
  have hR : rayleigh (normalizedLaplacian cheegerEdgeAdj)
      (degreeSqrt cheegerEdgeAdj *ᵥ (![1, 2] : Fin 2 → ℝ)) = 1 / 5 := by
    have hne : (![1, 2] : Fin 2 → ℝ) ≠ 0 := by
      intro h
      have h0 : (![1, 2] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
      simp at h0
    rw [rayleigh_normalizedLaplacian_degreeSqrt cheegerEdgeAdj ichv_edge_pos_deg
      hne, laplacian_quadForm cheegerEdgeAdj cheegerEdgeAdj_symmetric
      (![1, 2] : Fin 2 → ℝ)]
    norm_num [Fin.sum_univ_two, cheegerEdgeAdj, deg, cheegerEdgeAdj_regular,
      Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.one_apply]
  refine ⟨?_, ?_, by rw [hR]; norm_num⟩
  · rintro ⟨S, hS, hSc, hfam, hle⟩
    have hf0 : (![1, 2] : Fin 2 → ℝ) 0 = 1 := by simp
    have hf1 : (![1, 2] : Fin 2 → ℝ) 1 = 2 := by simp
    have hcond : conductance cheegerEdgeAdj S = 1 := by
      rcases hfam with ⟨t, ht⟩ | ⟨t, ht⟩
      · -- superlevel: {1} only (1 < t excludes 0 without taking all)
        rcases le_or_lt t 1 with h | h
        · exfalso
          have hU : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
            intro i
            fin_cases i
            · exact (ht 0).2 (by rw [hf0]; linarith)
            · exact (ht 1).2 (by rw [hf1]; linarith))
          rw [hU] at hSc
          simp at hSc
        · -- 1 < t: 0 ∉ S; nonempty forces 1 ∈ S (t ≤ 2)
          have h0n : (0 : Fin 2) ∉ S := by
            intro h0
            have hc0 := (ht 0).1 h0
            rw [hf0] at hc0
            linarith
          obtain ⟨iS, hiS⟩ := hS
          have h1S : (1 : Fin 2) ∈ S := by
            fin_cases iS
            · exact absurd hiS h0n
            · exact hiS
          have hSetEq : S = ({1} : Finset (Fin 2)) := by
            refine Finset.ext fun i => ?_
            constructor
            · intro hi
              fin_cases i
              · exact absurd hi h0n
              · simp
            · intro hi
              have hi1 : i = (1 : Fin 2) := Finset.mem_singleton.1 hi
              rw [hi1]
              exact h1S
          rw [hSetEq]
          exact vsc_edge_cond_singleton 1
      · -- sublevel: {0} only
        rcases le_or_lt 2 t with h | h
        · exfalso
          have hU : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
            intro i
            fin_cases i
            · exact (ht 0).2 (by rw [hf0]; linarith)
            · exact (ht 1).2 (by rw [hf1]; linarith))
          rw [hU] at hSc
          simp at hSc
        · -- t < 2: 1 ∉ S; nonempty forces 0 ∈ S (1 ≤ t)
          have h1n : (1 : Fin 2) ∉ S := by
            intro h1
            have hc1 := (ht 1).1 h1
            rw [hf1] at hc1
            linarith
          obtain ⟨iS, hiS⟩ := hS
          have h0S : (0 : Fin 2) ∈ S := by
            fin_cases iS
            · exact hiS
            · exact absurd hiS h1n
          have hSetEq : S = ({0} : Finset (Fin 2)) := by
            refine Finset.ext fun i => ?_
            constructor
            · intro hi
              fin_cases i
              · simp
              · exact absurd hi h1n
            · intro hi
              have hi0 : i = (0 : Fin 2) := Finset.mem_singleton.1 hi
              rw [hi0]
              exact h0S
          rw [hSetEq]
          exact vsc_edge_cond_singleton 0
    rw [hcond, hR] at hle
    norm_num at hle
  · rw [Fin.sum_univ_two, cheegerEdgeAdj_regular 0, cheegerEdgeAdj_regular 1]
    norm_num


/-!
### The irregular Fiedler instantiation QA (2026-08-26)

The family's algorithm-facing capstone — `fiedler_sweep_cut_normalized`
— exercised on both fixtures at *exact* spectral pins, plus the new
lower pin that makes `λ₂ (L_sym P₃) = 1` exact (the `≥ 1` side is new:
every admissible Rayleigh quotient is at least `1`, the slack being the
sum-of-squares `2 · x₁²` at the constraint `x₀ + √2 x₁ + x₂ = 0`), the
pullback algebra and the constraint hinge pinned raw at the concrete
eigenpair, and the connectivity mechanism fenced on the disconnected
fixture (`λ₂ = 0` pinned; a kernel eigenvector provably violates the
orthogonality hinge the constraint conversion needs).
-/

/-- **The exact `λ₂` pin, `≥ 1` side (new)**: every admissible Rayleigh
quotient of `L_sym (P₃)` is at least `1`. The constraint set of the sInf
engine at the true kernel vector is `x ⊥ (1, √2, 1)`, i.e. `x₀ + √2 x₁
+ x₂ = 0`; substituting `x₀ + x₂ = -√2 x₁` in the entrywise quadratic
form leaves the slack `2 x₁² ≥ 0`. -/
theorem icPathAdj_secondEval_ge_one :
    1 ≤ secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 3)) := by
  have hentry : ∀ i j : Fin 3,
      normalizedLaplacian icPathAdj i j
        = (if i = j then (1 : ℝ) else 0)
          - (Real.sqrt (deg icPathAdj i))⁻¹ * icPathAdj i j
            * (Real.sqrt (deg icPathAdj j))⁻¹ := by
    intro i j
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
      Matrix.diagonal_apply]
  have hquad : ∀ x : Fin 3 → ℝ,
      quadForm (normalizedLaplacian icPathAdj) x
        = x 0 * x 0 + x 1 * x 1 + x 2 * x 2
          - 2 * (Real.sqrt 2)⁻¹ * (x 0 * x 1 + x 1 * x 2) := by
    intro x
    have hdeglit : ∀ i : Fin 3,
        deg !![0, 1, 0; 1, 0, 1; 0, 1, 0] i = if i = 1 then 2 else 1 := by
      intro i
      fin_cases i <;> simp [deg, Fin.sum_univ_three]
      all_goals norm_num
    simp only [quadForm, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_three, hentry]
    simp [icPathAdj, hdeglit, Real.sqrt_one]
    ring
  rw [secondEval_variational_of_ker
    (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
    (normalizedLaplacian_psd icPathAdj icPathAdj_symmetric icPathAdj_nonneg
      icPathAdj_pos_deg)
    icPathAdj_kernelVec_ne
    (normalizedLaplacian_mulVec_degreeSqrt_onesVec icPathAdj
      icPathAdj_pos_deg)
    (by decide)]
  have hbound : ∀ r ∈ {r : ℝ | ∃ x : Fin 3 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x (degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ))
        = 0 ∧
      rayleigh (normalizedLaplacian icPathAdj) x = r}, 1 ≤ r := by
    rintro r ⟨x, hx0, hxorth, hxr⟩
    have hc : x 0 + Real.sqrt 2 * x 1 + x 2 = 0 := by
      simp only [Matrix.dotProduct, icPathAdj_kernelVec,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] at hxorth
      norm_num at hxorth
      linear_combination hxorth
    have hdp : 0 < Matrix.dotProduct x x := by
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, x i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx0 (funext hcon)
      have h1 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ x j * x j :=
        fun j _ => mul_self_nonneg (x j)
      have h2 : 0 < x i * x i := mul_self_pos.2 hi
      simpa [Matrix.dotProduct] using
        Finset.sum_pos' h1 ⟨i, Finset.mem_univ i, h2⟩
    have hdn : Matrix.dotProduct x x
        = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 := by
      simp [Matrix.dotProduct, Fin.sum_univ_three]
    have hqn : quadForm (normalizedLaplacian icPathAdj) x
        = Matrix.dotProduct x x + 2 * x 1 ^ 2 := by
      have hx02 : x 0 + x 2 = -(Real.sqrt 2 * x 1) := by linarith
      have hs0 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      have hscalar : 2 * (Real.sqrt 2)⁻¹ * (x 1 * (-(Real.sqrt 2 * x 1)))
          = -(2 * x 1 ^ 2) := by
        rw [show 2 * (Real.sqrt 2)⁻¹ * (x 1 * (-(Real.sqrt 2 * x 1)))
              = -2 * ((Real.sqrt 2)⁻¹ * Real.sqrt 2) * (x 1 * x 1) from by
              ring,
          inv_mul_cancel₀ hs0]
        ring
      rw [hquad x, hdn,
        show x 0 * x 1 + x 1 * x 2 = x 1 * (x 0 + x 2) from by ring, hx02]
      linarith
    rw [← hxr, rayleigh, if_neg hx0, hqn]
    calc (1 : ℝ) = Matrix.dotProduct x x / Matrix.dotProduct x x :=
        by exact (div_self hdp.ne').symm
      _ ≤ (Matrix.dotProduct x x + 2 * x 1 ^ 2) / Matrix.dotProduct x x := by
          exact div_le_div_of_nonneg_right
            (by linarith [sq_nonneg (x 1)]) hdp.le
  have hne : {r : ℝ | ∃ x : Fin 3 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x (degreeSqrt icPathAdj *ᵥ (onesVec : Fin 3 → ℝ))
        = 0 ∧
      rayleigh (normalizedLaplacian icPathAdj) x = r}.Nonempty := by
    refine ⟨1, icEigVec, icEigVec_ne_zero, icEigVec_ortho_kernel, ?_⟩
    rw [rayleigh, if_neg icEigVec_ne_zero,
      show quadForm (normalizedLaplacian icPathAdj) icEigVec
          = Matrix.dotProduct icEigVec
              (normalizedLaplacian icPathAdj *ᵥ icEigVec) from rfl,
      icPathAdj_normLap_mulVec_eigVec, icEigVec_dot_self]
    ring
  exact le_csInf hne hbound

/-- **The exact pin: `λ₂ (L_sym P₃) = 1`.** The `≤ 1` side is the
file's eigenpair witness (delivered with the easy direction, before any
of the Fiedler family); the `≥ 1` side is new (the sum-of-squares
above). The family's Cheeger bracket on `P₃` now collapses to a point:
`φ²/2 = 1/2 ≤ λ₂ = 1 ≤ 2φ = 2`. -/
theorem icPathAdj_secondEval_eq_one :
    secondEval (normalizedLaplacian icPathAdj)
        (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
        (by decide : 2 ≤ Fintype.card (Fin 3)) = 1 :=
  le_antisymm icPathAdj_secondEval_le_one icPathAdj_secondEval_ge_one

/-- **The theorem instance on `P₃`, at the exact pin.** The returned
cut is a genuine swept level set of the (choice-defined) sweep vector,
nonempty and proper, with `conductance S ^ 2 ≤ 2 * λ₂ = 2 * 1`; joining
to the file's exhaustive-cut pin, its conductance is exactly `1` — so
the instance reads `1 ≤ 2` at both ends pinned independently of the
Fiedler family (`≤ 1` by the eigenpair witness, `≥ 1` by the
sum-of-squares). -/
theorem ifc_p3_instance_QA :
    ∃ S : Finset (Fin 3), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance icPathAdj S ^ 2
        ≤ 2 * secondEval (normalizedLaplacian icPathAdj)
            (normalizedLaplacian_symmetric icPathAdj icPathAdj_symmetric)
            (by decide : 2 ≤ Fintype.card (Fin 3))
      ∧ conductance icPathAdj S = 1 := by
  obtain ⟨S, hSne, hScne, _hlev, hcond⟩ :=
    fiedler_sweep_cut_normalized icPathAdj icPathAdj_symmetric
      icPathAdj_nonneg icPathAdj_pos_deg
      (by decide : 2 ≤ Fintype.card (Fin 3)) icP3_supportGraph_connected
  exact ⟨S, hSne, hScne, hcond, icPathAdj_conductance_all S hSne hScne⟩

/-- **The theorem instance on `K₂`, against the pinned classical
`λ₂ = 2`.** On two vertices a nonempty proper set is a singleton, so
the file's singleton-conductance pin applies: the instance reads
`conductance S ^ 2 = 1 ≤ 2 * 2 = 4` — the regular family's own
`fiedler_sweep_cut` constant on the cone (`2 λ₂ (L) / d = 4` at
`λ₂ = 2`, `d = 1`). -/
theorem ifc_edge_instance_QA :
    ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance cheegerEdgeAdj S ^ 2
        ≤ 2 * secondEval (normalizedLaplacian cheegerEdgeAdj)
            (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
            (le_refl 2)
      ∧ conductance cheegerEdgeAdj S = 1 := by
  obtain ⟨S, hSne, hScne, _hlev, hcond⟩ :=
    fiedler_sweep_cut_normalized cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg
      icEdge_pos_deg (le_refl 2) icK2_supportGraph_connected
  have hsum : S.card + Sᶜ.card = Fintype.card (Fin 2) :=
    Finset.card_add_card_compl S
  have hcard2 : Fintype.card (Fin 2) = 2 := rfl
  have hle : S.card ≤ 1 := by
    have h1 : 1 ≤ Sᶜ.card := Finset.card_pos.2 hScne
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1 (le_antisymm hle
    (Finset.card_pos.2 hSne))
  have hS : S = ({i} : Finset (Fin 2)) := hi
  exact ⟨S, hSne, hScne, hcond, by rw [hS]; exact vsc_edge_cond_singleton i⟩

/-- **The stretch cancellation, raw.** Pulling the concrete eigenpair
witness `![1, 0, -1]` back through `1/√D` and stretching again
recovers it — the identity `fiedlerSweepVector_degreeSqrt_mulVec` uses,
verified entrywise at the fixture's mixed degrees `1, 2, 1`. -/
theorem ifc_pullback_cancel_raw_QA :
    degreeSqrt icPathAdj *ᵥ (degreeInvSqrt icPathAdj *ᵥ icEigVec)
      = icEigVec := by
  funext i
  fin_cases i
  all_goals simp [degreeSqrt_mulVec_apply, degreeInvSqrt_mulVec_apply,
    icEigVec, icPathAdj_deg, Real.sqrt_one]

/-- **The constraint hinge, raw.** The pullback of the concrete
eigenpair witness is degree-weighted zero-sum — the sweep family's own
hypothesis, here verified through the pairing identity and the file's
independent orthogonality pin `icEigVec_ortho_kernel` (the same hinge
`fiedlerSweepVector_sum_deg_eq_zero` exercises at the choice-defined
Fiedler vector, computed at a witness any reader can check). -/
theorem ifc_pullback_zero_sum_raw_QA :
    ∑ i, deg icPathAdj i * (degreeInvSqrt icPathAdj *ᵥ icEigVec) i = 0 := by
  rw [← dotProduct_degreeSqrt_mulVec_onesVec icPathAdj
      (fun i => le_of_lt (icPathAdj_pos_deg i)),
    ifc_pullback_cancel_raw_QA]
  exact icEigVec_ortho_kernel

/-- The block indicator `![1, 1, 0, 0]` is a combinatorial kernel
vector of the disconnected fixture (positive weights never cross
blocks). -/
theorem ifc_disc_block_indicator_kernel :
    (laplacian icDiscAdj) *ᵥ (![1, 1, 0, 0] : Fin 4 → ℝ) = 0 := by
  have hv : ∀ i j : Fin 4, 0 < icDiscAdj i j →
      (![1, 1, 0, 0] : Fin 4 → ℝ) i = (![1, 1, 0, 0] : Fin 4 → ℝ) j := by
    intro i j hij
    have hb := icDiscAdj_blocks i j hij
    have hval : ∀ k : Fin 4, (![1, 1, 0, 0] : Fin 4 → ℝ) k
        = if (k : ℕ) ≤ 1 then 1 else 0 := by
      intro k
      fin_cases k <;> rfl
    rw [hval i, hval j]
    by_cases hi : (i : ℕ) ≤ 1
    · have hj : (j : ℕ) ≤ 1 := by simpa [hi] using hb
      simp [hi, hj]
    · have hj : ¬((j : ℕ) ≤ 1) := by simpa [hi] using hb
      simp [hi, hj]
  funext i
  rw [laplacian_mulVec_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rcases eq_or_lt_of_le (icDiscAdj_nonneg i j) with h0 | hpos
  · rw [← h0, zero_mul]
  · rw [hv i j hpos, sub_self, mul_zero]

/-- Every degree of the disconnected fixture is exactly `1`. -/
theorem ifc_disc_deg_one : ∀ i, deg icDiscAdj i = 1 := by
  intro i
  fin_cases i <;> simp [deg, icDiscAdj, Fin.sum_univ_four] <;> decide

/-- **The connectivity mechanism, fenced.** On the disconnected fixture
`λ₂ (L_sym) = 0` (the file's two-route pin), and here is a nonzero
kernel eigenvector of `L_sym` — the kind of vector the Fiedler index
selects at a zero second eigenvalue — whose pairing with the true
kernel vector `√D · 1` is `2 ≠ 0`: kernel vectors provably need *not*
satisfy the orthogonality hinge. This is exactly where connectivity
enters `fiedler_sweep_cut_normalized`: `0 < λ₂` (not kernel-ness) is
what discharges the constraint conversion, and on this fixture that
hypothesis fails. -/
theorem ifc_disc_hinge_fence_QA :
    ∃ u : Fin 4 → ℝ, u ≠ 0 ∧ normalizedLaplacian icDiscAdj *ᵥ u = 0 ∧
      Matrix.dotProduct u (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))
        ≠ 0
      ∧ secondEval (normalizedLaplacian icDiscAdj)
          (normalizedLaplacian_symmetric icDiscAdj icDiscAdj_symmetric)
          (by norm_num) = 0 := by
  refine ⟨degreeSqrt icDiscAdj *ᵥ (![1, 1, 0, 0] : Fin 4 → ℝ), ?_, ?_, ?_,
    icDisc_secondEval_eq_zero⟩
  · intro h
    have h1 := congrFun h 1
    rw [degreeSqrt_mulVec_apply, ifc_disc_deg_one, Real.sqrt_one,
      one_mul] at h1
    simp at h1
  · exact normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero
      icDiscAdj icDiscAdj_pos_deg ifc_disc_block_indicator_kernel
  · simp only [Matrix.dotProduct, degreeSqrt_mulVec_apply, onesVec,
      mul_one, Fin.sum_univ_four, ifc_disc_deg_one, Real.sqrt_one]
    norm_num


section IrregularFences

/-! ### The signed fixture's easy-direction and sweep clauses -/

/-- **Fence (easy direction, `hnn`)**: at the signed two-vertex fixture
every other hypothesis of `cheeger_upper_bound_normalized` is genuine
(symmetry, degrees `1 = 2 - 1 > 0`, two vertices), and the
nonnegativity-dropped conclusion reads `λ₂ = 0 ≤ 2φ = -2` — false. -/
theorem icf_easy_hnn_fence_QA :
    ¬ (secondEval (normalizedLaplacian ichSigAdj)
        (normalizedLaplacian_symmetric ichSigAdj ichSigAdj_symmetric)
        (le_refl 2)
      ≤ 2 * cheegerConstant ichSigAdj) := by
  rw [ichSigAdj_secondEval, ichSigAdj_cheegerConstant]
  norm_num

/-- Isolation companion: every other clause genuine, `hnn` exactly the
failure. -/
theorem icf_easy_hnn_isolation_QA :
    ichSigAdj.IsSymm
      ∧ (∀ i, 0 < deg ichSigAdj i)
      ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ ¬ (∀ i j, 0 ≤ ichSigAdj i j) :=
  ⟨ichSigAdj_symmetric, ichSigAdj_pos_deg, by norm_num,
    ichSigAdj_not_nonneg⟩

/-- The degree stretch is the identity at the signed fixture (degrees
`1`). -/
theorem icf_sig_stretch (f : Fin 2 → ℝ) :
    degreeSqrt ichSigAdj *ᵥ f = f := by
  funext i
  rw [degreeSqrt_mulVec_apply, ichSigAdj_deg i, Real.sqrt_one, one_mul]

/-- The signed fixture's Rayleigh pin at the antisymmetric mode: `R =
-2` (the PSD-broken spectral side goes negative). -/
theorem icf_sig_rayleigh :
    rayleigh (normalizedLaplacian ichSigAdj)
      (degreeSqrt ichSigAdj *ᵥ (![1, -1] : Fin 2 → ℝ)) = -2 := by
  have hne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  rw [icf_sig_stretch, rayleigh, if_neg hne, quadForm, ichSigAdj_normLap]
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.of_apply]
  norm_num

/-- **Fence (sweep lemma, `hnn`)**: at the signed fixture with the
degree-orthogonal mode `f = ![1, -1]` (orthogonality genuine:
`∑ deg · f = 0`), the nonnegativity-dropped conclusion reads
`φ²/2 = 1/2 ≤ R = -2` — false. -/
theorem icf_sweep_hnn_fence_QA :
    ¬ (cheegerConstant ichSigAdj ^ 2 / 2
        ≤ rayleigh (normalizedLaplacian ichSigAdj)
            (degreeSqrt ichSigAdj *ᵥ (![1, -1] : Fin 2 → ℝ))) := by
  rw [ichSigAdj_cheegerConstant, icf_sig_rayleigh]
  norm_num

theorem icf_sweep_hnn_isolation_QA :
    ichSigAdj.IsSymm
      ∧ (∀ i, 0 < deg ichSigAdj i)
      ∧ ((![1, -1] : Fin 2 → ℝ) ≠ 0)
      ∧ ∑ i, deg ichSigAdj i * (![1, -1] : Fin 2 → ℝ) i = 0
      ∧ ¬ (∀ i j, 0 ≤ ichSigAdj i j) :=
  ⟨ichSigAdj_symmetric, ichSigAdj_pos_deg, by
      intro h
      have h0 := congrFun h 0
      simp at h0, by
      rw [Fin.sum_univ_two, ichSigAdj_deg 0, ichSigAdj_deg 1]
      norm_num, ichSigAdj_not_nonneg⟩

/-- **Fence (cut theorem, `hnn`)**: at the same instantiation the
dropped conclusion fails for *every* candidate cut — the bound clause
alone refutes it, since `2 * R = -4` while conductances square back
nonnegative. -/
theorem icf_cut_hnn_fence_QA :
    ¬ (∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ (![1, -1] : Fin 2 → ℝ) i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ (![1, -1] : Fin 2 → ℝ) i ≤ t)) ∧
      conductance ichSigAdj S ^ 2
        ≤ 2 * rayleigh (normalizedLaplacian ichSigAdj)
            (degreeSqrt ichSigAdj *ᵥ (![1, -1] : Fin 2 → ℝ))) := by
  rintro ⟨S, -, -, -, hle⟩
  rw [icf_sig_rayleigh] at hle
  have hnn : (0 : ℝ) ≤ conductance ichSigAdj S ^ 2 := sq_nonneg _
  linarith

/-! ### The edge fixture's sweep and extraction clauses -/

/-- The raw Rayleigh pin the `horth` fence reuses: `R = 1/5` at
`f = ![1, 2]` on `K₂` (Dirichlet energy `1`, squared norm `5`). -/
theorem icf_edge_rayleigh_f12 :
    rayleigh (normalizedLaplacian cheegerEdgeAdj)
      (degreeSqrt cheegerEdgeAdj *ᵥ (![1, 2] : Fin 2 → ℝ)) = 1 / 5 := by
  have hne : (![1, 2] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  rw [rayleigh_normalizedLaplacian_degreeSqrt cheegerEdgeAdj ichv_edge_pos_deg
    hne, laplacian_quadForm cheegerEdgeAdj cheegerEdgeAdj_symmetric
      (![1, 2] : Fin 2 → ℝ)]
  norm_num [Fin.sum_univ_two, cheegerEdgeAdj, deg, cheegerEdgeAdj_regular,
    Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.one_apply]

/-- **Fence (sweep lemma, `horth`)**: at `f = ![1, 2]` on `K₂` the
degree-weighted zero-sum clause fails (`∑ deg · f = 3`), and the
dropped conclusion reads `φ²/2 = 1/2 ≤ R = 1/5` — false. -/
theorem icf_sweep_horth_fence_QA :
    ¬ (cheegerConstant cheegerEdgeAdj ^ 2 / 2
        ≤ rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (![1, 2] : Fin 2 → ℝ))) := by
  rw [edge_cheegerConstant, icf_edge_rayleigh_f12]
  norm_num

theorem icf_sweep_horth_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ ((![1, 2] : Fin 2 → ℝ) ≠ 0)
      ∧ ∑ i, deg cheegerEdgeAdj i * (![1, 2] : Fin 2 → ℝ) i = 3 :=
  ⟨cheegerEdgeAdj_symmetric, cheegerEdgeAdj_nonneg, ichv_edge_pos_deg, by
      intro h
      have h0 := congrFun h 0
      simp at h0, by
      rw [Fin.sum_univ_two, cheegerEdgeAdj_regular 0, cheegerEdgeAdj_regular 1]
      norm_num⟩

/-- **Fence (sweep lemma, `hf0`)**: at `f = 0` the orthogonality clause
is trivially genuine (`∑ deg · 0 = 0`) while `rayleigh` at the zero
vector is the definitional junk `0`, so the dropped conclusion reads
`φ²/2 = 1/2 ≤ 0` — false. -/
theorem icf_sweep_hf0_fence_QA :
    ¬ (cheegerConstant cheegerEdgeAdj ^ 2 / 2
        ≤ rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (0 : Fin 2 → ℝ))) := by
  rw [edge_cheegerConstant]
  simp only [Matrix.mulVec_zero, rayleigh, if_pos rfl]
  norm_num

theorem icf_sweep_hf0_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ ∑ i, deg cheegerEdgeAdj i * (0 : Fin 2 → ℝ) i = 0 :=
  ⟨cheegerEdgeAdj_symmetric, cheegerEdgeAdj_nonneg, ichv_edge_pos_deg, by
    simp⟩

/-- The shared shape refutation: no nonempty proper superlevel or
sublevel set of a constant function exists. -/
private theorem icf_no_proper_level_of_const {V₂ : Type} [Fintype V₂]
    [DecidableEq V₂] (c : ℝ) (S : Finset V₂)
    (hSne : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hlev : (∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ c)
      ∨ (∃ t : ℝ, ∀ i, i ∈ S ↔ c ≤ t)) : False := by
  obtain ⟨i₀, hi₀⟩ := hSne
  rcases hlev with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hti : t ≤ c := (ht i₀).1 hi₀
    have hU : S = Finset.univ :=
      Finset.eq_univ_iff_forall.2 fun i => (ht i).2 hti
    rw [hU] at hSc
    simp at hSc
  · have hti : c ≤ t := (ht i₀).1 hi₀
    have hU : S = Finset.univ :=
      Finset.eq_univ_iff_forall.2 fun i => (ht i).2 hti
    rw [hU] at hSc
    simp at hSc

/-- **Fence (cut theorem, `hf0`)**: the swept superlevel/sublevel
family of a constant function contains no nonempty proper member at
all, so the dropped conclusion fails on the *shape* clauses — a
witness shape distinct from the `horth` fence's. -/
theorem icf_cut_hf0_fence_QA :
    ¬ (∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ (0 : Fin 2 → ℝ) i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ (0 : Fin 2 → ℝ) i ≤ t)) ∧
      conductance cheegerEdgeAdj S ^ 2
        ≤ 2 * rayleigh (normalizedLaplacian cheegerEdgeAdj)
            (degreeSqrt cheegerEdgeAdj *ᵥ (0 : Fin 2 → ℝ))) := by
  rintro ⟨S, hSne, hSc, hlev, -⟩
  rcases hlev with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact icf_no_proper_level_of_const (0 : ℝ) S hSne hSc
      (Or.inl ⟨t, fun i => by simpa using ht i⟩)
  · exact icf_no_proper_level_of_const (0 : ℝ) S hSne hSc
      (Or.inr ⟨t, fun i => by simpa using ht i⟩)

theorem icf_cut_hf0_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ ∑ i, deg cheegerEdgeAdj i * (0 : Fin 2 → ℝ) i = 0 :=
  icf_sweep_hf0_isolation_QA

/-! ### The degree-window and sandwich clauses (wrong constants) -/

/-- The combinatorial and normalized Laplacians coincide on `K₂`
(degrees `1`), so the file's normalized pin `λ₂ (L_sym) = 2` transfers
to `lambda2`. -/
theorem icf_edge_lambda2 :
    lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2) = 2 := by
  have hL : (laplacian cheegerEdgeAdj : Matrix (Fin 2) (Fin 2) ℝ)
      = normalizedLaplacian cheegerEdgeAdj := by
    refine Matrix.ext fun i j => ?_
    have hdeg : deg cheegerEdgeAdj i = 1 := cheegerEdgeAdj_regular i
    have hl : laplacian cheegerEdgeAdj i j
        = (if i = j then (1 : ℝ) else 0) - cheegerEdgeAdj i j := by
      simp only [laplacian, degreeMatrix, Matrix.sub_apply,
        Matrix.of_apply, hdeg]
      congr 1
    have hn : normalizedLaplacian cheegerEdgeAdj i j
        = (if i = j then (1 : ℝ) else 0) - cheegerEdgeAdj i j := by
      rw [normalizedLaplacian_eq_regularNormalizedLaplacian cheegerEdgeAdj 1
        cheegerEdgeAdj_regular (by norm_num)]
      simp only [regularNormalizedLaplacian, Matrix.sub_apply,
        Matrix.one_apply, Matrix.smul_apply, inv_one, one_smul,
        smul_eq_mul]
    rw [hl, hn]
  have h1 : lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2)
      = evals (laplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          ⟨1, by norm_num⟩ := rfl
  have h2 : evals (laplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        ⟨1, by norm_num⟩
      = evals (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          ⟨1, by norm_num⟩ :=
    evals_congr _ _ hL _
  have h3 : evals (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        ⟨1, by norm_num⟩
      = secondEval (normalizedLaplacian cheegerEdgeAdj)
          (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          (le_refl 2) := rfl
  rw [h1, h2, h3]
  exact icEdge_normLap_secondEval

/-- **Fence (sandwich floor, `hdmin`)**: the wrong-constant fence — an
overstating `dmin` cannot inflate the bound. At `dmin = 5` on `K₂`
(every degree `1`, so `5 ≤ deg` fails) the dropped conclusion reads
`5 · λ₂(L_sym) = 10 ≤ λ₂(L) = 2` — false. -/
theorem icf_sandwich_hdmin_fence_QA :
    ¬ (5 * secondEval (normalizedLaplacian cheegerEdgeAdj)
          (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          (le_refl 2)
        ≤ lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2)) := by
  rw [icEdge_normLap_secondEval, icf_edge_lambda2]
  norm_num

theorem icf_sandwich_hdmin_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ (0 < (5 : ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ ¬ (∀ i, (5 : ℝ) ≤ deg cheegerEdgeAdj i) :=
  ⟨cheegerEdgeAdj_symmetric, cheegerEdgeAdj_nonneg, ichv_edge_pos_deg, by norm_num,
    by norm_num, by
      intro h
      have h0 := h 0
      rw [cheegerEdgeAdj_regular 0] at h0
      norm_num at h0⟩

/-- **Fence (sandwich ceiling, `hdmax`)**: at `dmax = 1/2` on `K₂`
(every degree `1`, so `deg ≤ 1/2` fails) the dropped conclusion reads
`λ₂(L) = 2 ≤ (1/2) · λ₂(L_sym) = 1` — false. -/
theorem icf_sandwich_hdmax_fence_QA :
    ¬ (lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2)
        ≤ (1 / 2) * secondEval (normalizedLaplacian cheegerEdgeAdj)
            (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
            (le_refl 2)) := by
  rw [icf_edge_lambda2, icEdge_normLap_secondEval]
  norm_num

theorem icf_sandwich_hdmax_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ ¬ (∀ i, deg cheegerEdgeAdj i ≤ (1 / 2 : ℝ)) :=
  ⟨cheegerEdgeAdj_symmetric, cheegerEdgeAdj_nonneg, ichv_edge_pos_deg, by norm_num,
    by
      intro h
      have h0 := h 0
      rw [cheegerEdgeAdj_regular 0] at h0
      norm_num at h0⟩

/-- **Fence (window floor, `hdmin`)**: at `dmin = 5` on `K₂` the
dropped conclusion reads `5 · φ²/2 = 5/2 ≤ λ₂(L) = 2` — false. -/
theorem icf_window_floor_hdmin_fence_QA :
    ¬ (5 * cheegerConstant cheegerEdgeAdj ^ 2 / 2
        ≤ lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2)) := by
  rw [edge_cheegerConstant, icf_edge_lambda2]
  norm_num

theorem icf_window_floor_hdmin_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ (0 < (5 : ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ ¬ (∀ i, (5 : ℝ) ≤ deg cheegerEdgeAdj i) :=
  icf_sandwich_hdmin_isolation_QA

/-- **Fence (window ceiling, `hdmax`)**: at `dmax = 1/2` on `K₂` the
dropped conclusion reads `λ₂(L) = 2 ≤ 2 · ((1/2) · φ) = 1` — false. -/
theorem icf_window_ceiling_hdmax_fence_QA :
    ¬ (lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2)
        ≤ 2 * ((1 / 2) * cheegerConstant cheegerEdgeAdj)) := by
  rw [icf_edge_lambda2, edge_cheegerConstant]
  norm_num

theorem icf_window_ceiling_hdmax_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ ¬ (∀ i, deg cheegerEdgeAdj i ≤ (1 / 2 : ℝ)) :=
  icf_sandwich_hdmax_isolation_QA

/-! ### The volume sweep extraction's `hy` and `hM` clauses -/

/-- **Fence (`hy`)**: at `y = 1` on `K₂` the minority-volume clause
fails at `t = 1` (the superlevel is everything: `2 · 2 ≤ 2`), and the
dropped conclusion fails on the shape clauses — `y ^ 2` is constant,
so no nonempty proper superlevel set exists. -/
theorem icf_extract_hy_fence_QA :
    ¬ (∃ S : Finset (Fin 2), ∃ t : ℝ, 0 < t ∧
        (∀ i, i ∈ S ↔ t ≤ (1 : Fin 2 → ℝ) i ^ 2) ∧
        S.Nonempty ∧ Sᶜ.Nonempty ∧
        conductance cheegerEdgeAdj S ^ 2
          ≤ (∑ i, ∑ j, cheegerEdgeAdj i j *
              ((1 : Fin 2 → ℝ) i - (1 : Fin 2 → ℝ) j) ^ 2)
            / (∑ i, deg cheegerEdgeAdj i * (1 : Fin 2 → ℝ) i ^ 2)) := by
  rintro ⟨S, t, ht, hmem, hSne, hSc, -⟩
  have hsq : ∀ i : Fin 2, (1 : Fin 2 → ℝ) i ^ 2 = (1 : ℝ) := by
    intro i
    simp
  exact icf_no_proper_level_of_const (1 : ℝ) S hSne hSc
    (Or.inl ⟨t, fun i => (hmem i).trans (by rw [hsq i])⟩)

theorem icf_extract_hy_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ 0 < ∑ i, deg cheegerEdgeAdj i * (1 : Fin 2 → ℝ) i ^ 2
      ∧ ¬ (∀ t : ℝ, 0 < t →
          2 * vol cheegerEdgeAdj
              (Finset.univ.filter (fun i => t ≤ (1 : Fin 2 → ℝ) i ^ 2))
            ≤ vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2))) :=
  ⟨cheegerEdgeAdj_symmetric, cheegerEdgeAdj_nonneg, ichv_edge_pos_deg, by
      have h2 : ∑ i, deg cheegerEdgeAdj i * (1 : Fin 2 → ℝ) i ^ 2 = 2 := by
        simp [cheegerEdgeAdj_regular]
      linarith, by
      intro h
      have h1 := h 1 (by norm_num)
      have hfilt : (Finset.univ.filter
          (fun i => (1 : ℝ) ≤ (1 : Fin 2 → ℝ) i ^ 2))
          = (Finset.univ : Finset (Fin 2)) := by
        ext i
        rw [Finset.mem_filter]
        simp
      rw [hfilt, ichv_edge_vol_univ] at h1
      norm_num at h1⟩

/-- **Fence (`hM`)**: at `y = 0` the minority clause is trivially
genuine (positive superlevels are empty) while the degree-weighted
mass clause fails (`∑ deg · 0 = 0`), and the dropped conclusion's
shape clauses fail outright — every superlevel at a positive level is
empty, so `S.Nonempty` cannot hold. -/
theorem icf_extract_hM_fence_QA :
    ¬ (∃ S : Finset (Fin 2), ∃ t : ℝ, 0 < t ∧
        (∀ i, i ∈ S ↔ t ≤ (0 : Fin 2 → ℝ) i ^ 2) ∧
        S.Nonempty ∧ Sᶜ.Nonempty ∧
        conductance cheegerEdgeAdj S ^ 2
          ≤ (∑ i, ∑ j, cheegerEdgeAdj i j *
              ((0 : Fin 2 → ℝ) i - (0 : Fin 2 → ℝ) j) ^ 2)
            / (∑ i, deg cheegerEdgeAdj i * (0 : Fin 2 → ℝ) i ^ 2)) := by
  rintro ⟨S, t, ht, hmem, ⟨i₀, hi₀⟩, -, -⟩
  have hle := (hmem i₀).1 hi₀
  simp only [Pi.zero_apply, pow_zero] at hle
  norm_num at hle
  have hempty : S = ∅ :=
    Finset.eq_empty_iff_forall_not_mem.2 fun i hi => by
      have hle' := (hmem i).1 hi
      simp only [Pi.zero_apply, pow_zero] at hle'
      norm_num at hle'
      linarith
  rw [hempty] at hi₀
  simp at hi₀

theorem icf_extract_hM_isolation_QA :
    cheegerEdgeAdj.IsSymm
      ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j)
      ∧ (∀ i, 0 < deg cheegerEdgeAdj i)
      ∧ (∀ t : ℝ, 0 < t →
          2 * vol cheegerEdgeAdj
              (Finset.univ.filter (fun i => t ≤ (0 : Fin 2 → ℝ) i ^ 2))
            ≤ vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2)))
      ∧ ∑ i, deg cheegerEdgeAdj i * (0 : Fin 2 → ℝ) i ^ 2 = 0 :=
  ⟨cheegerEdgeAdj_symmetric, cheegerEdgeAdj_nonneg, ichv_edge_pos_deg, by
      intro t ht
      have hfilt : (Finset.univ.filter
          (fun i => t ≤ (0 : Fin 2 → ℝ) i ^ 2)) = (∅ : Finset (Fin 2)) := by
        ext i
        rw [Finset.mem_filter]
        constructor
        · intro hi
          have hle := hi.2
          simp only [Pi.zero_apply, pow_zero] at hle
          norm_num at hle
          linarith
        · intro hi
          exact absurd hi (by simp)
      rw [hfilt, vol_empty, ichv_edge_vol_univ]
      norm_num, by
      simp⟩

/-! ### The kernel iff's `hconn` clause (disconnected fixture) -/

/-- The block-indicator kernel witness at the combinatorial operator. -/
theorem icf_disc_lap_kernel :
    (laplacian icDiscAdj) *ᵥ (![1, 1, 0, 0] : Fin 4 → ℝ) = 0 := by
  have hv : ∀ i j : Fin 4, 0 < icDiscAdj i j →
      (![1, 1, 0, 0] : Fin 4 → ℝ) i = (![1, 1, 0, 0] : Fin 4 → ℝ) j := by
    intro i j hij
    have hb := icDiscAdj_blocks i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  funext i
  rw [laplacian_mulVec_apply]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rcases eq_or_lt_of_le (icDiscAdj_nonneg i j) with h0 | hpos
  · rw [← h0, zero_mul]
  · rw [hv i j hpos, sub_self, mul_zero]

theorem icf_disc_kernel_witness :
    normalizedLaplacian icDiscAdj *ᵥ (![1, 1, 0, 0] : Fin 4 → ℝ) = 0 := by
  have h1 : degreeSqrt icDiscAdj *ᵥ (![1, 1, 0, 0] : Fin 4 → ℝ)
      = (![1, 1, 0, 0] : Fin 4 → ℝ) := by
    funext i
    rw [degreeSqrt_mulVec_apply, ifc_disc_deg_one i, Real.sqrt_one,
      one_mul]
  rw [← h1]
  exact normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero
    icDiscAdj icDiscAdj_pos_deg icf_disc_lap_kernel

/-- **Fence (kernel iff, `hconn`)**: on the disconnected two-edge
fixture the component indicator is a kernel vector of `L_sym` that is
not a multiple of the stretched constants `√D · 1` (degrees all `1`,
so the stretched constants are the constant vector) — the forward
direction of the `hconn`-dropped iff fails. -/
theorem icf_kernel_iff_hconn_fence_QA :
    ¬ (normalizedLaplacian icDiscAdj *ᵥ (![1, 1, 0, 0] : Fin 4 → ℝ) = 0
        ↔ ∃ c : ℝ, (![1, 1, 0, 0] : Fin 4 → ℝ)
          = c • (degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ))) := by
  intro hiff
  obtain ⟨c, hc⟩ := hiff.1 icf_disc_kernel_witness
  have hones : degreeSqrt icDiscAdj *ᵥ (onesVec : Fin 4 → ℝ)
      = (1 : Fin 4 → ℝ) := by
    funext i
    rw [degreeSqrt_mulVec_apply, ifc_disc_deg_one i, Real.sqrt_one,
      onesVec]
    simp
  rw [hones] at hc
  have h0 := congrFun hc 0
  have h2 := congrFun hc 2
  simp at h0 h2
  linarith

theorem icf_kernel_iff_hconn_isolation_QA :
    icDiscAdj.IsSymm
      ∧ (∀ i j, 0 ≤ icDiscAdj i j)
      ∧ (∀ i, 0 < deg icDiscAdj i)
      ∧ ¬ (supportGraph icDiscAdj icDiscAdj_symmetric).Connected :=
  ⟨icDiscAdj_symmetric, icDiscAdj_nonneg, icDiscAdj_pos_deg,
    icDiscAdj_not_connected⟩

/-! ### The Cheeger-consumer corollary's `hconn` and `hnn` clauses -/

/-- **Fence (positivity corollary, `hconn`)**: on the disconnected
two-edge fixture the first component `{0, 1}` is a nonempty proper cut
of boundary `0` and positive volumes, so `φ ≤ 0` and the
connectivity-dropped conclusion `0 < φ` fails. -/
theorem icf_cheeger_pos_hconn_fence_QA :
    ¬ (0 < cheegerConstant icDiscAdj) := by
  have hcut : conductance icDiscAdj ({0, 1} : Finset (Fin 4)) = 0 := by
    have hcompl : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    have hbd : boundary icDiscAdj ({0, 1} : Finset (Fin 4)) = 0 := by
      rw [boundary, hcompl]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Finset.sum_eq_zero fun j _ => ?_]
      fin_cases i <;> fin_cases j <;> simp_all [icDiscAdj] <;> omega
    have hv1 : vol icDiscAdj ({0, 1} : Finset (Fin 4)) = 2 := by
      simp [vol, ifc_disc_deg_one]
    have hv2 : vol icDiscAdj ({0, 1} : Finset (Fin 4))ᶜ = 2 := by
      rw [hcompl]
      simp [vol, ifc_disc_deg_one]
    rw [conductance, hbd, hv1, hv2]
    norm_num
  have hle := conductance_ge_cheegerConstant icDiscAdj icDiscAdj_nonneg
    ({0, 1} : Finset (Fin 4)) (by decide) (by decide)
  rw [hcut] at hle
  exact not_lt.2 (hle.trans (by norm_num))

theorem icf_cheeger_pos_hconn_isolation_QA :
    icDiscAdj.IsSymm
      ∧ (∀ i j, 0 ≤ icDiscAdj i j)
      ∧ (∀ i, 0 < deg icDiscAdj i)
      ∧ 2 ≤ Fintype.card (Fin 4)
      ∧ ¬ (supportGraph icDiscAdj icDiscAdj_symmetric).Connected :=
  ⟨icDiscAdj_symmetric, icDiscAdj_nonneg, icDiscAdj_pos_deg, by norm_num,
    icDiscAdj_not_connected⟩

/-- The negative-cut fixture: symmetric, connected through the positive
edges `(0,1)` and `(1,2)`, degrees `(1, 2, 1)` all positive, one
negative off-diagonal `(0,2) = -3`. -/
def icNegCutAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3, 1, -3; 1, 0, 1; -3, 1, 3]

theorem icNegCutAdj_symmetric : icNegCutAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [icNegCutAdj]

theorem icNegCutAdj_deg : ∀ i, deg icNegCutAdj i = if i = 1 then 2 else 1 := by
  intro i
  fin_cases i
  all_goals simp [deg, icNegCutAdj, Fin.sum_univ_three]
  all_goals norm_num

theorem icNegCutAdj_pos_deg : ∀ i, 0 < deg icNegCutAdj i := by
  intro i
  rw [icNegCutAdj_deg]
  fin_cases i <;> simp

theorem icNegCutAdj_not_nonneg : ¬ (∀ i j, 0 ≤ icNegCutAdj i j) := by
  intro h
  have h02 := h 0 2
  simp [icNegCutAdj] at h02
  linarith

theorem icNegCutAdj_adj01 :
    (supportGraph icNegCutAdj icNegCutAdj_symmetric).Adj (0 : Fin 3) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [icNegCutAdj]⟩

theorem icNegCutAdj_adj12 :
    (supportGraph icNegCutAdj icNegCutAdj_symmetric).Adj (1 : Fin 3) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [icNegCutAdj]⟩

theorem icNegCutAdj_connected :
    (supportGraph icNegCutAdj icNegCutAdj_symmetric).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons icNegCutAdj_adj01 SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons icNegCutAdj_adj01
      (SimpleGraph.Walk.cons icNegCutAdj_adj12 SimpleGraph.Walk.nil)⟩

/-- **Fence (positivity corollary, `hnn`)**: on the connected
negative-cut fixture the cut `{0}` has boundary `1 - 3 = -2` at unit
volume, so `φ ≤ -2 < 0` and the nonnegativity-dropped conclusion
`0 < φ` fails. -/
theorem icf_cheeger_pos_hnn_fence_QA :
    ¬ (0 < cheegerConstant icNegCutAdj) := by
  have hcut : conductance icNegCutAdj ({0} : Finset (Fin 3)) = -2 := by
    have hcompl : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
    have hbd : boundary icNegCutAdj ({0} : Finset (Fin 3)) = -2 := by
      rw [boundary, hcompl]
      simp [icNegCutAdj]
      norm_num
    have hv1 : vol icNegCutAdj ({0} : Finset (Fin 3)) = 1 := by
      rw [vol, Finset.sum_singleton, icNegCutAdj_deg]
      norm_num
    have hv2 : vol icNegCutAdj ({0} : Finset (Fin 3))ᶜ = 3 := by
      rw [hcompl]
      simp [vol, icNegCutAdj_deg]
      norm_num
    rw [conductance, hbd, hv1, hv2]
    norm_num
  have hbdd : BddBelow {c : ℝ | ∃ S : Finset (Fin 3), S.Nonempty ∧
      Sᶜ.Nonempty ∧ conductance icNegCutAdj S = c} := by
    have hsub : {c : ℝ | ∃ S : Finset (Fin 3), S.Nonempty ∧ Sᶜ.Nonempty ∧
        conductance icNegCutAdj S = c}
        ⊆ Set.range (fun S : Finset (Fin 3) => conductance icNegCutAdj S) := by
      rintro c ⟨S, -, -, rfl⟩
      exact ⟨S, rfl⟩
    exact (Set.Finite.subset (Set.finite_range _) hsub).bddBelow
  have hle : cheegerConstant icNegCutAdj
      ≤ conductance icNegCutAdj ({0} : Finset (Fin 3)) :=
    csInf_le hbdd ⟨{0}, by decide, by decide, rfl⟩
  rw [hcut] at hle
  exact not_lt.2 (hle.trans (by norm_num))

theorem icf_cheeger_pos_hnn_isolation_QA :
    icNegCutAdj.IsSymm
      ∧ (∀ i, 0 < deg icNegCutAdj i)
      ∧ 2 ≤ Fintype.card (Fin 3)
      ∧ (supportGraph icNegCutAdj icNegCutAdj_symmetric).Connected
      ∧ ¬ (∀ i j, 0 ≤ icNegCutAdj i j) :=
  ⟨icNegCutAdj_symmetric, icNegCutAdj_pos_deg, by decide,
    icNegCutAdj_connected, icNegCutAdj_not_nonneg⟩

/-! ### The disconnected-λ₂ theorem's `hnn` and `hd` clauses -/

/-- Two disjoint copies of the signed fixture on `Fin 4`: symmetric,
degrees all `1`, disconnected, one negative entry per block. -/
def icSigDisc4Adj : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, -1, 0, 0; -1, 2, 0, 0; 0, 0, 2, -1; 0, 0, -1, 2]

theorem icSigDisc4Adj_symmetric : icSigDisc4Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [icSigDisc4Adj, Matrix.vecHead, Matrix.vecTail]

theorem icSigDisc4Adj_deg : ∀ i, deg icSigDisc4Adj i = 1 := by
  intro i
  fin_cases i
  all_goals simp [deg, icSigDisc4Adj, Fin.sum_univ_four]
  all_goals norm_num

theorem icSigDisc4Adj_pos_deg : ∀ i, 0 < deg icSigDisc4Adj i := by
  intro i
  rw [icSigDisc4Adj_deg]
  norm_num

theorem icSigDisc4Adj_not_nonneg : ¬ (∀ i j, 0 ≤ icSigDisc4Adj i j) := by
  intro h
  have h01 := h 0 1
  simp [icSigDisc4Adj] at h01
  linarith

theorem icSigDisc4Adj_blocks (i j : Fin 4) (h : 0 < icSigDisc4Adj i j) :
    decide ((i : ℕ) ≤ 1) = decide ((j : ℕ) ≤ 1) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [icSigDisc4Adj, Matrix.vecHead, Matrix.vecTail]

theorem icSigDisc4_walk_blocks {u v : Fin 4}
    (w : (supportGraph icSigDisc4Adj icSigDisc4Adj_symmetric).Walk u v) :
    decide ((u : ℕ) ≤ 1) = decide ((v : ℕ) ≤ 1) := by
  induction w with
  | nil => rfl
  | cons hadj _ ih =>
    exact (icSigDisc4Adj_blocks _ _ ((supportGraph_adj.1 hadj).2)).trans ih

theorem icSigDisc4Adj_not_connected :
    ¬(supportGraph icSigDisc4Adj icSigDisc4Adj_symmetric).Connected := by
  intro hconn
  obtain ⟨w⟩ := hconn 0 2
  have hb := icSigDisc4_walk_blocks w
  exact absurd hb (by decide)

/-- The entry form of the fixture's normalized Laplacian (degrees all
`1`, so the degree scaling is trivial): `L_sym = 1 - A`. -/
theorem icSigDisc4Adj_normLap_entry (i j : Fin 4) :
    normalizedLaplacian icSigDisc4Adj i j
      = (if i = j then (1 : ℝ) else 0) - icSigDisc4Adj i j := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply, icSigDisc4Adj_deg, Real.sqrt_one, inv_one,
    one_mul, mul_one]

/-- The two block-antisymmetric modes are eigenvectors at exactly
`-2` (`L_sym` is block-diagonal with the signed fixture's blocks). -/
theorem icSigDisc4Adj_mulVec_minus :
    normalizedLaplacian icSigDisc4Adj *ᵥ (![1, -1, 0, 0] : Fin 4 → ℝ)
      = (-2 : ℝ) • (![1, -1, 0, 0] : Fin 4 → ℝ) := by
  have hentry : ∀ i j : Fin 4,
      normalizedLaplacian icSigDisc4Adj i j
        = (if i = j then (1 : ℝ) else 0) - icSigDisc4Adj i j :=
    icSigDisc4Adj_normLap_entry
  funext i
  fin_cases i <;>
    simp only [hentry, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
  all_goals simp [icSigDisc4Adj_deg, icSigDisc4Adj, Real.sqrt_one, inv_one]
  all_goals norm_num

theorem icSigDisc4Adj_mulVec_minus' :
    normalizedLaplacian icSigDisc4Adj *ᵥ (![0, 0, 1, -1] : Fin 4 → ℝ)
      = (-2 : ℝ) • (![0, 0, 1, -1] : Fin 4 → ℝ) := by
  have hentry : ∀ i j : Fin 4,
      normalizedLaplacian icSigDisc4Adj i j
        = (if i = j then (1 : ℝ) else 0) - icSigDisc4Adj i j :=
    icSigDisc4Adj_normLap_entry
  funext i
  fin_cases i <;>
    simp only [hentry, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
  all_goals simp [icSigDisc4Adj_deg, icSigDisc4Adj, Real.sqrt_one, inv_one]
  all_goals norm_num

theorem icSigDisc4_dot_self_one :
    Matrix.dotProduct (![1, -1, 0, 0] : Fin 4 → ℝ)
      (![1, -1, 0, 0] : Fin 4 → ℝ) = 2 := by
  simp [Matrix.dotProduct, Fin.sum_univ_four]
  norm_num

theorem icSigDisc4_dot_self_two :
    Matrix.dotProduct (![0, 0, 1, -1] : Fin 4 → ℝ)
      (![0, 0, 1, -1] : Fin 4 → ℝ) = 2 := by
  simp [Matrix.dotProduct, Fin.sum_univ_four]
  norm_num

theorem icSigDisc4_dot_cross :
    Matrix.dotProduct (![1, -1, 0, 0] : Fin 4 → ℝ)
      (![0, 0, 1, -1] : Fin 4 → ℝ) = 0 := by
  simp [Matrix.dotProduct, Fin.sum_univ_four]

theorem icSigDisc4_dot_cross' :
    Matrix.dotProduct (![0, 0, 1, -1] : Fin 4 → ℝ)
      (![1, -1, 0, 0] : Fin 4 → ℝ) = 0 := by
  rw [Matrix.dotProduct_comm]
  exact icSigDisc4_dot_cross

private theorem icSigDisc4_li :
    LinearIndependent ℝ
      (fun k : Fin 2 => (fun i : Fin 4 =>
        if k = 0 then (![1, -1, 0, 0] : Fin 4 → ℝ) i
        else (![0, 0, 1, -1] : Fin 4 → ℝ) i) :
        Fin 2 → (Fin 4 → ℝ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc 0
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_two] at h0 h2
  fin_cases i
  · exact h0
  · exact h2

/-- `evals ⟨1⟩ ≤ -2` by the subspace Rayleigh–Ritz engine at the two
block-antisymmetric modes (both eigenvectors at exactly `-2`). -/
theorem icSigDisc4_evals_one_le :
    evals (normalizedLaplacian_symmetric icSigDisc4Adj
      icSigDisc4Adj_symmetric) ⟨1, by norm_num⟩ ≤ -2 := by
  refine evals_le_of_linearIndependent
    (normalizedLaplacian_symmetric icSigDisc4Adj icSigDisc4Adj_symmetric)
    (k := 2) (by norm_num) (by norm_num) icSigDisc4_li ?_
  intro c
  have hX : (∑ l : Fin 2, c l •
      (fun k : Fin 2 => (fun i : Fin 4 =>
        if k = 0 then (![1, -1, 0, 0] : Fin 4 → ℝ) i
        else (![0, 0, 1, -1] : Fin 4 → ℝ) i) :
        Fin 2 → (Fin 4 → ℝ)) l)
      = c 0 • (![1, -1, 0, 0] : Fin 4 → ℝ)
        + c 1 • (![0, 0, 1, -1] : Fin 4 → ℝ) := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_two]
  have hMX : normalizedLaplacian icSigDisc4Adj *ᵥ
      (c 0 • (![1, -1, 0, 0] : Fin 4 → ℝ)
        + c 1 • (![0, 0, 1, -1] : Fin 4 → ℝ))
      = (-2 * c 0) • (![1, -1, 0, 0] : Fin 4 → ℝ)
        + (-2 * c 1) • (![0, 0, 1, -1] : Fin 4 → ℝ) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      icSigDisc4Adj_mulVec_minus, icSigDisc4Adj_mulVec_minus',
      smul_smul, smul_smul, mul_comm (c 0) (-2 : ℝ),
      mul_comm (c 1) (-2 : ℝ)]
  have hM : quadForm (normalizedLaplacian icSigDisc4Adj)
      (∑ l : Fin 2, c l •
        (fun k : Fin 2 => (fun i : Fin 4 =>
          if k = 0 then (![1, -1, 0, 0] : Fin 4 → ℝ) i
          else (![0, 0, 1, -1] : Fin 4 → ℝ) i) :
          Fin 2 → (Fin 4 → ℝ)) l)
      = -4 * (c 0 * c 0) - 4 * (c 1 * c 1) := by
    rw [hX, quadForm, hMX]
    simp only [Matrix.add_dotProduct, Matrix.dotProduct_add,
      Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
      icSigDisc4_dot_self_one, icSigDisc4_dot_self_two,
      icSigDisc4_dot_cross, icSigDisc4_dot_cross']
    ring
  have hD : Matrix.dotProduct (∑ l : Fin 2, c l •
      (fun k : Fin 2 => (fun i : Fin 4 =>
        if k = 0 then (![1, -1, 0, 0] : Fin 4 → ℝ) i
        else (![0, 0, 1, -1] : Fin 4 → ℝ) i) :
        Fin 2 → (Fin 4 → ℝ)) l)
      (∑ l : Fin 2, c l •
        (fun k : Fin 2 => (fun i : Fin 4 =>
          if k = 0 then (![1, -1, 0, 0] : Fin 4 → ℝ) i
          else (![0, 0, 1, -1] : Fin 4 → ℝ) i) :
          Fin 2 → (Fin 4 → ℝ)) l)
      = 2 * (c 0 * c 0) + 2 * (c 1 * c 1) := by
    rw [hX]
    simp only [Matrix.add_dotProduct, Matrix.dotProduct_add,
      Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
      icSigDisc4_dot_self_one, icSigDisc4_dot_self_two,
      icSigDisc4_dot_cross, icSigDisc4_dot_cross']
    ring
  rw [hM, hD]
  linarith [sq_nonneg (c 0), sq_nonneg (c 1)]

/-- **Fence (disconnected-λ₂ theorem, `hnn`)**: at the two disjoint
signed blocks the spectrum of `L_sym` carries the signed fixture's
`-2` twice (both block-antisymmetric modes are eigenvectors at exactly
`-2`), so `λ₂ ≤ -2 ≠ 0` and the nonnegativity-dropped conclusion
`λ₂ = 0` fails. -/
theorem icf_disc4_hnn_fence_QA :
    ¬ (secondEval (normalizedLaplacian icSigDisc4Adj)
        (normalizedLaplacian_symmetric icSigDisc4Adj icSigDisc4Adj_symmetric)
        (by norm_num)
      = 0) := by
  have hle : secondEval (normalizedLaplacian icSigDisc4Adj)
      (normalizedLaplacian_symmetric icSigDisc4Adj icSigDisc4Adj_symmetric)
      (by norm_num)
      ≤ -2 := icSigDisc4_evals_one_le
  intro heq
  rw [heq] at hle
  norm_num at hle

theorem icf_disc4_hnn_isolation_QA :
    icSigDisc4Adj.IsSymm
      ∧ (∀ i, 0 < deg icSigDisc4Adj i)
      ∧ 2 ≤ Fintype.card (Fin 4)
      ∧ ¬ (supportGraph icSigDisc4Adj icSigDisc4Adj_symmetric).Connected
      ∧ ¬ (∀ i j, 0 ≤ icSigDisc4Adj i j) :=
  ⟨icSigDisc4Adj_symmetric, icSigDisc4Adj_pos_deg, by norm_num,
    icSigDisc4Adj_not_connected, icSigDisc4Adj_not_nonneg⟩

/-- The edge-plus-isolated-vertex fixture on `Fin 3`: symmetric,
nonnegative, degrees `(1, 1, 0)`. -/
def icIsoAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 ∨ (i : ℕ) = 1 ∧ (j : ℕ) = 0 then 1 else 0

theorem icIsoAdj_symmetric : icIsoAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [icIsoAdj]

theorem icIsoAdj_nonneg : ∀ i j, 0 ≤ icIsoAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [icIsoAdj]

theorem icIsoAdj_deg : ∀ i, deg icIsoAdj i = if (i : ℕ) = 2 then 0 else 1 := by
  intro i
  fin_cases i
  all_goals simp only [deg, Fin.sum_univ_three, icIsoAdj, Matrix.of_apply]
  all_goals norm_num

theorem icIsoAdj_not_pos_deg : ¬ (∀ i, 0 < deg icIsoAdj i) := by
  intro h
  have h2 := h 2
  rw [icIsoAdj_deg] at h2
  simp at h2

theorem icIsoAdj_not_connected :
    ¬(supportGraph icIsoAdj icIsoAdj_symmetric).Connected := by
  have hadj : ∀ i j : Fin 3,
      (supportGraph icIsoAdj icIsoAdj_symmetric).Adj i j → j ≠ 2 := by
    intro i j hadj
    rw [supportGraph_adj] at hadj
    intro hj2
    rw [hj2] at hadj
    have := hadj.2
    simp [icIsoAdj] at this
  have hnot : ∀ (u v : Fin 3),
      (supportGraph icIsoAdj icIsoAdj_symmetric).Walk u v → v = 2 → u = 2 := by
    intro u v w
    induction w with
    | nil => intro hv; exact hv
    | cons hadj' rest ih =>
        intro hv
        exact absurd (ih hv) (hadj _ _ hadj')
  intro hconn
  obtain ⟨w⟩ := hconn 0 2
  exact absurd (hnot 0 2 w rfl) (by decide)

/-- The entry form of the fixture's normalized Laplacian: the isolated
vertex's junk `D⁻¹ᐟ² = 0` scaling makes its `L_sym` eigenvalue `1`,
not `0`. -/
theorem icIsoAdj_normLap (i j : Fin 3) :
    normalizedLaplacian icIsoAdj i j
      = if (i : ℕ) = 0 ∧ (j : ℕ) = 1 ∨ (i : ℕ) = 1 ∧ (j : ℕ) = 0 then -1
        else if i = j then 1 else 0 := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply, icIsoAdj_deg]
  fin_cases i <;> fin_cases j <;>
    simp [icIsoAdj, Real.sqrt_one, Real.sqrt_zero]

theorem icIsoAdj_mulVec (x : Fin 3 → ℝ) :
    normalizedLaplacian icIsoAdj *ᵥ x = ![x 0 - x 1, x 1 - x 0, x 2] := by
  funext i
  fin_cases i
  all_goals simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
    icIsoAdj_normLap]
  all_goals ring

theorem icIsoAdj_psd : ∀ x : Fin 3 → ℝ,
    0 ≤ quadForm (normalizedLaplacian icIsoAdj) x := by
  intro x
  rw [quadForm, icIsoAdj_mulVec]
  simp [Matrix.dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 2)]

theorem icIsoAdj_kernel :
    normalizedLaplacian icIsoAdj *ᵥ (![1, 1, 0] : Fin 3 → ℝ) = 0 := by
  rw [icIsoAdj_mulVec]
  funext i
  fin_cases i <;> simp

theorem icIsoAdj_kernel_ne : (![1, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- `λ₂ (L_sym) ≥ 1` by the variational engine (PSD and the kernel
supplied by hand — no shelf degree lemma applies at the failing `hd`):
every admissible constraint quotient equals `(4 x₀² + x₂²)/(2 x₀² +
x₂²) ≥ 1`. -/
theorem icIsoAdj_secondEval_ge_one :
    1 ≤ secondEval (normalizedLaplacian icIsoAdj)
        (normalizedLaplacian_symmetric icIsoAdj icIsoAdj_symmetric)
        (by decide) := by
  rw [secondEval_variational_of_ker
    (normalizedLaplacian_symmetric icIsoAdj icIsoAdj_symmetric)
    icIsoAdj_psd icIsoAdj_kernel_ne icIsoAdj_kernel (by decide)]
  refine le_csInf ?_ ?_
  · refine ⟨1, ![0, 0, 1], by
        intro h
        have h2 := congrFun h 2
        simp at h2, ?_, ?_⟩
    · rw [show Matrix.dotProduct (![0, 0, 1] : Fin 3 → ℝ)
          (![1, 1, 0] : Fin 3 → ℝ)
          = (0 : ℝ) from by
        simp [Matrix.dotProduct, Fin.sum_univ_three]]
    · rw [rayleigh, if_neg (by
          intro h
          have h2 := congrFun h 2
          simp at h2)]
      have hq : quadForm (normalizedLaplacian icIsoAdj)
          (![0, 0, 1] : Fin 3 → ℝ) = 1 := by
        rw [quadForm, icIsoAdj_mulVec]
        simp [Matrix.dotProduct, Fin.sum_univ_three]
      have hd : Matrix.dotProduct (![0, 0, 1] : Fin 3 → ℝ)
          (![0, 0, 1] : Fin 3 → ℝ) = 1 := by
        simp [Matrix.dotProduct, Fin.sum_univ_three]
      rw [hq, hd]
      norm_num
  · rintro r ⟨x, hx0, hxorth, hxr⟩
    have hc : x 0 + x 1 = 0 := by
      simpa [Matrix.dotProduct, Fin.sum_univ_three] using hxorth
    have hx1 : x 1 = -(x 0) := by linarith
    have hq : quadForm (normalizedLaplacian icIsoAdj) x
        = 4 * (x 0 * x 0) + x 2 * x 2 := by
      rw [quadForm, icIsoAdj_mulVec]
      simp [Matrix.dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      rw [hx1]
      ring
    have hd : Matrix.dotProduct x x
        = 2 * (x 0 * x 0) + x 2 * x 2 := by
      simp [Matrix.dotProduct, Fin.sum_univ_three]
      rw [hx1]
      ring
    have hdp : 0 < Matrix.dotProduct x x := by
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, x i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx0 (funext hcon)
      have h1 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ x j * x j :=
        fun j _ => mul_self_nonneg (x j)
      have h2 : 0 < x i * x i := mul_self_pos.2 hi
      simpa [Matrix.dotProduct] using
        Finset.sum_pos' h1 ⟨i, Finset.mem_univ i, h2⟩
    rw [← hxr, rayleigh, if_neg hx0, hq, le_div_iff₀ hdp, hd]
    nlinarith [sq_nonneg (x 0)]

/-- **Fence (disconnected-λ₂ theorem, `hd`)**: at the
edge-plus-isolated-vertex fixture every other hypothesis is genuine
(symmetry, nonnegativity, at least two vertices, disconnected), while
`λ₂ (L_sym) = 1 ≠ 0` — the isolated vertex's junk `D⁻¹ᐟ² = 0` row
makes its eigenvalue `1`, not `0`, and the degree-dropped conclusion
fails. -/
theorem icf_iso_hd_fence_QA :
    ¬ (secondEval (normalizedLaplacian icIsoAdj)
        (normalizedLaplacian_symmetric icIsoAdj icIsoAdj_symmetric)
        (by decide)
      = 0) := by
  intro heq
  have h := icIsoAdj_secondEval_ge_one
  rw [heq] at h
  norm_num at h

theorem icf_iso_hd_isolation_QA :
    icIsoAdj.IsSymm
      ∧ (∀ i j, 0 ≤ icIsoAdj i j)
      ∧ 2 ≤ Fintype.card (Fin 3)
      ∧ ¬ (supportGraph icIsoAdj icIsoAdj_symmetric).Connected
      ∧ ¬ (∀ i, 0 < deg icIsoAdj i) :=
  ⟨icIsoAdj_symmetric, icIsoAdj_nonneg, by decide,
    icIsoAdj_not_connected, icIsoAdj_not_pos_deg⟩

/-! ### The Fiedler capstone's `hnn` clause (the negative-cut fixture) -/

theorem icNegCut_sq_sqrt_two : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

theorem icNegCut_sqrt_two_ne : Real.sqrt 2 ≠ 0 :=
  Real.sqrt_ne_zero'.2 (by norm_num)

theorem icNegCut_inv_sqrt_two_mul_sqrt_two :
    (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1 :=
  inv_mul_cancel₀ icNegCut_sqrt_two_ne

theorem icNegCut_two_inv_sqrt_two : 2 * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
  field_simp

/-- The entry form of the fixture's normalized Laplacian (degrees
`(1, 2, 1)`, so the middle row/column carries the `√2` scaling). -/
theorem icNegCutAdj_normLap_entry (i j : Fin 3) :
    normalizedLaplacian icNegCutAdj i j
      = (if i = j then (1 : ℝ) else 0)
        - (Real.sqrt (deg icNegCutAdj i))⁻¹ * icNegCutAdj i j
          * (Real.sqrt (deg icNegCutAdj j))⁻¹ := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply]

/-- The three eigenvector witnesses: `(1, 0, -1)` at `-5`, `(1, √2, 1)`
at `0`, `(1, -√2, 1)` at `2`. -/
theorem icNegCutAdj_mulVec_minus :
    normalizedLaplacian icNegCutAdj *ᵥ (![1, 0, -1] : Fin 3 → ℝ)
      = (-5 : ℝ) • (![1, 0, -1] : Fin 3 → ℝ) := by
  have hentry := icNegCutAdj_normLap_entry
  funext i
  fin_cases i <;>
    simp only [hentry, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
  all_goals simp only [icNegCutAdj_deg, Real.sqrt_one, inv_one, mul_one,
    one_mul]
  all_goals simp [icNegCutAdj, icNegCut_inv_sqrt_two_mul_sqrt_two]
  all_goals (try norm_num)

theorem icNegCutAdj_mulVec_zero :
    normalizedLaplacian icNegCutAdj *ᵥ (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      = 0 := by
  have hentry := icNegCutAdj_normLap_entry
  funext i
  fin_cases i <;>
    simp only [hentry, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.head_cons, Pi.zero_apply]
  all_goals simp only [icNegCutAdj_deg, Real.sqrt_one, inv_one, mul_one,
    one_mul]
  all_goals simp [icNegCutAdj, icNegCut_inv_sqrt_two_mul_sqrt_two]
  all_goals (try norm_num)
  all_goals (try linarith [icNegCut_two_inv_sqrt_two])

theorem icNegCutAdj_mulVec_plus :
    normalizedLaplacian icNegCutAdj *ᵥ (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ)
      = (2 : ℝ) • (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) := by
  have hentry := icNegCutAdj_normLap_entry
  funext i
  fin_cases i <;>
    simp only [hentry, Matrix.mulVec, Matrix.dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.head_cons, Pi.smul_apply, smul_eq_mul]
  all_goals simp only [icNegCutAdj_deg, Real.sqrt_one, inv_one, mul_one,
    one_mul, neg_mul]
  all_goals simp [icNegCutAdj, icNegCut_inv_sqrt_two_mul_sqrt_two]
  all_goals (try norm_num)
  all_goals (try linarith [icNegCut_two_inv_sqrt_two])

/-- The pairwise dot products of the witness trio: self dots `2, 4, 4`,
cross dots all zero. -/
theorem icNegCutAdj_dot_minus_minus :
    Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ) (![1, 0, -1] : Fin 3 → ℝ)
      = 2 := by
  simp [Matrix.dotProduct, Fin.sum_univ_three]
  norm_num

theorem icNegCutAdj_dot_zero_zero :
    Matrix.dotProduct (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) = 4 := by
  have hexp : Matrix.dotProduct (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      = (1 : ℝ) * 1 + Real.sqrt 2 * Real.sqrt 2 + 1 * 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_three]
  rw [hexp, icNegCut_sq_sqrt_two]
  norm_num

theorem icNegCutAdj_dot_plus_plus :
    Matrix.dotProduct (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) = 4 := by
  have hexp : Matrix.dotProduct (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ)
      = (1 : ℝ) * 1 + (-Real.sqrt 2) * (-Real.sqrt 2) + 1 * 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_three]
  rw [hexp, neg_mul_neg, icNegCut_sq_sqrt_two]
  norm_num

theorem icNegCutAdj_dot_minus_zero :
    Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ)
      (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) = 0 := by
  simp [Matrix.dotProduct, Fin.sum_univ_three]

theorem icNegCutAdj_dot_zero_minus :
    Matrix.dotProduct (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, 0, -1] : Fin 3 → ℝ) = 0 := by
  rw [Matrix.dotProduct_comm]
  exact icNegCutAdj_dot_minus_zero

theorem icNegCutAdj_dot_minus_plus :
    Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ)
      (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) = 0 := by
  simp [Matrix.dotProduct, Fin.sum_univ_three]

theorem icNegCutAdj_dot_plus_minus :
    Matrix.dotProduct (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, 0, -1] : Fin 3 → ℝ) = 0 := by
  rw [Matrix.dotProduct_comm]
  exact icNegCutAdj_dot_minus_plus

theorem icNegCutAdj_dot_zero_plus :
    Matrix.dotProduct (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) = 0 := by
  have hexp : Matrix.dotProduct (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ)
      = (1 : ℝ) * 1 + Real.sqrt 2 * (-Real.sqrt 2) + 1 * 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_three]
  rw [hexp, mul_neg, icNegCut_sq_sqrt_two]
  norm_num

theorem icNegCutAdj_dot_plus_zero :
    Matrix.dotProduct (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ)
      (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) = 0 := by
  rw [Matrix.dotProduct_comm]
  exact icNegCutAdj_dot_zero_plus

private theorem icNegCut_li1 :
    LinearIndependent ℝ
      (fun _ : Fin 1 => (![1, 0, -1] : Fin 3 → ℝ) : Fin 1 → (Fin 3 → ℝ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc 0
  simp at h0
  fin_cases i
  · exact h0

private theorem icNegCut_li2 :
    LinearIndependent ℝ
      (fun k : Fin 2 => (fun i : Fin 3 =>
        if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
        else (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
        Fin 2 → (Fin 3 → ℝ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc 0
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_two] at h0 h2
  fin_cases i
  · show c 0 = 0
    linarith
  · show c 1 = 0
    linarith

private theorem icNegCut_li3 :
    LinearIndependent ℝ
      (fun k : Fin 3 => (fun i : Fin 3 =>
        if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
        else if k = 1 then (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i
        else (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
        Fin 3 → (Fin 3 → ℝ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hE0 : c 0 + c 1 + c 2 = 0 := by
    have hh := congrFun hc 0
    simp [Fin.sum_univ_three] at hh
    exact hh
  have hE1 : Real.sqrt 2 * (c 1 - c 2) = 0 := by
    have hh := congrFun hc 1
    simp [Fin.sum_univ_three] at hh
    linear_combination hh
  have hE2 : -(c 0) + c 1 + c 2 = 0 := by
    have hh := congrFun hc 2
    simp [Fin.sum_univ_three] at hh
    exact hh
  have hc12 : c 1 - c 2 = 0 := by
    rcases mul_eq_zero.1 hE1 with h | h
    · exact absurd h icNegCut_sqrt_two_ne
    · exact h
  have hc0 : c 0 = 0 := by
    have h2c0 : (2 : ℝ) * c 0 = 0 := by linear_combination hE0 - hE2
    linarith
  have hc1 : c 1 = 0 := by
    have h2c1 : (2 : ℝ) * c 1 = 0 := by
      linear_combination hE0 + hc12 - hc0
    linarith
  fin_cases i
  · exact hc0
  · exact hc1
  · show c 2 = 0
    linarith

/-- `evals ⟨0⟩ ≤ -5`: the bottom mode alone (the engine at `k = 1`,
its bound attained with equality on the mode's span). -/
theorem icNegCut_evals_zero_le :
    evals (normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric)
      ⟨0, by norm_num⟩ ≤ -5 := by
  refine evals_le_of_linearIndependent
    (normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric)
    (k := 1) (by norm_num) (by norm_num) icNegCut_li1 ?_
  intro c
  have hX : (∑ l : Fin 1, c l •
      (fun _ : Fin 1 => (![1, 0, -1] : Fin 3 → ℝ) : Fin 1 → (Fin 3 → ℝ)) l)
      = c 0 • (![1, 0, -1] : Fin 3 → ℝ) := by
    simp
  have hM : quadForm (normalizedLaplacian icNegCutAdj)
      (∑ l : Fin 1, c l •
        (fun _ : Fin 1 => (![1, 0, -1] : Fin 3 → ℝ) : Fin 1 → (Fin 3 → ℝ)) l)
      = -10 * (c 0 * c 0) := by
    rw [hX, quadForm, Matrix.mulVec_smul, icNegCutAdj_mulVec_minus,
      smul_smul]
    simp only [Matrix.dotProduct_smul, Matrix.smul_dotProduct,
      smul_eq_mul, icNegCutAdj_dot_minus_minus]
    ring
  have hD : Matrix.dotProduct
      (∑ l : Fin 1, c l •
        (fun _ : Fin 1 => (![1, 0, -1] : Fin 3 → ℝ) : Fin 1 → (Fin 3 → ℝ)) l)
      (∑ l : Fin 1, c l •
        (fun _ : Fin 1 => (![1, 0, -1] : Fin 3 → ℝ) : Fin 1 → (Fin 3 → ℝ)) l)
      = 2 * (c 0 * c 0) := by
    rw [hX]
    simp only [Matrix.dotProduct_smul, Matrix.smul_dotProduct,
      smul_eq_mul, icNegCutAdj_dot_minus_minus]
    ring
  rw [hM, hD]
  linarith [sq_nonneg (c 0)]

/-- `evals ⟨1⟩ ≤ 0`: the bottom mode plus the kernel mode. -/
theorem icNegCut_evals_one_le :
    evals (normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric)
      ⟨1, by norm_num⟩ ≤ 0 := by
  refine evals_le_of_linearIndependent
    (normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric)
    (k := 2) (by norm_num) (by norm_num) icNegCut_li2 ?_
  intro c
  have hX : (∑ l : Fin 2, c l •
      (fun k : Fin 2 => (fun i : Fin 3 =>
        if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
        else (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
        Fin 2 → (Fin 3 → ℝ)) l)
      = c 0 • (![1, 0, -1] : Fin 3 → ℝ)
        + c 1 • (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_two]
  have hMX : normalizedLaplacian icNegCutAdj *ᵥ
      (c 0 • (![1, 0, -1] : Fin 3 → ℝ)
        + c 1 • (![1, Real.sqrt 2, 1] : Fin 3 → ℝ))
      = (-5 * c 0) • (![1, 0, -1] : Fin 3 → ℝ) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      icNegCutAdj_mulVec_minus, icNegCutAdj_mulVec_zero, smul_zero,
      add_zero, smul_smul, mul_comm (c 0) (-5 : ℝ)]
  have hM : quadForm (normalizedLaplacian icNegCutAdj)
      (∑ l : Fin 2, c l •
        (fun k : Fin 2 => (fun i : Fin 3 =>
          if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
          else (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
          Fin 2 → (Fin 3 → ℝ)) l)
      = -10 * (c 0 * c 0) := by
    rw [hX, quadForm, hMX]
    simp only [Matrix.add_dotProduct, Matrix.dotProduct_add,
      Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
      icNegCutAdj_dot_minus_minus, icNegCutAdj_dot_zero_minus]
    ring
  have hD : Matrix.dotProduct
      (∑ l : Fin 2, c l •
        (fun k : Fin 2 => (fun i : Fin 3 =>
          if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
          else (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
          Fin 2 → (Fin 3 → ℝ)) l)
      (∑ l : Fin 2, c l •
        (fun k : Fin 2 => (fun i : Fin 3 =>
          if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
          else (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
          Fin 2 → (Fin 3 → ℝ)) l)
      = 2 * (c 0 * c 0) + 4 * (c 1 * c 1) := by
    rw [hX]
    simp only [Matrix.add_dotProduct, Matrix.dotProduct_add,
      Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
      icNegCutAdj_dot_minus_minus, icNegCutAdj_dot_zero_zero,
      icNegCutAdj_dot_minus_zero, icNegCutAdj_dot_zero_minus]
    ring
  rw [hM, hD]
  linarith [sq_nonneg (c 0)]

/-- `evals ⟨2⟩ ≤ 2`: the full witness trio (the spectrum is exactly
`{-5, 0, 2}`). -/
theorem icNegCut_evals_two_le :
    evals (normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric)
      ⟨2, by norm_num⟩ ≤ 2 := by
  refine evals_le_of_linearIndependent
    (normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric)
    (k := 3) (by norm_num) (by norm_num) icNegCut_li3 ?_
  intro c
  have hX : (∑ l : Fin 3, c l •
      (fun k : Fin 3 => (fun i : Fin 3 =>
        if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
        else if k = 1 then (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i
        else (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
        Fin 3 → (Fin 3 → ℝ)) l)
      = c 0 • (![1, 0, -1] : Fin 3 → ℝ)
        + c 1 • (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
        + c 2 • (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_three]
  have hMX : normalizedLaplacian icNegCutAdj *ᵥ
      (c 0 • (![1, 0, -1] : Fin 3 → ℝ)
        + c 1 • (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
        + c 2 • (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ))
      = (-5 * c 0) • (![1, 0, -1] : Fin 3 → ℝ)
        + (2 * c 2) • (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, icNegCutAdj_mulVec_minus,
      icNegCutAdj_mulVec_zero, icNegCutAdj_mulVec_plus, smul_zero,
      add_zero, smul_smul, smul_smul, mul_comm (c 0) (-5 : ℝ),
      mul_comm (c 2) (2 : ℝ)]
  have hM : quadForm (normalizedLaplacian icNegCutAdj)
      (∑ l : Fin 3, c l •
        (fun k : Fin 3 => (fun i : Fin 3 =>
          if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
          else if k = 1 then (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i
          else (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
          Fin 3 → (Fin 3 → ℝ)) l)
      = -10 * (c 0 * c 0) + 8 * (c 2 * c 2) := by
    rw [hX, quadForm, hMX]
    simp only [Matrix.add_dotProduct, Matrix.dotProduct_add,
      Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
      icNegCutAdj_dot_minus_minus, icNegCutAdj_dot_plus_plus,
      icNegCutAdj_dot_minus_plus, icNegCutAdj_dot_plus_minus,
      icNegCutAdj_dot_minus_zero, icNegCutAdj_dot_zero_minus,
      icNegCutAdj_dot_zero_plus, icNegCutAdj_dot_plus_zero]
    ring
  have hD : Matrix.dotProduct
      (∑ l : Fin 3, c l •
        (fun k : Fin 3 => (fun i : Fin 3 =>
          if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
          else if k = 1 then (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i
          else (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
          Fin 3 → (Fin 3 → ℝ)) l)
      (∑ l : Fin 3, c l •
        (fun k : Fin 3 => (fun i : Fin 3 =>
          if k = 0 then (![1, 0, -1] : Fin 3 → ℝ) i
          else if k = 1 then (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) i
          else (![1, -Real.sqrt 2, 1] : Fin 3 → ℝ) i) :
          Fin 3 → (Fin 3 → ℝ)) l)
      = 2 * (c 0 * c 0) + 4 * (c 1 * c 1) + 4 * (c 2 * c 2) := by
    rw [hX]
    simp only [Matrix.add_dotProduct, Matrix.dotProduct_add,
      Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
      icNegCutAdj_dot_minus_minus, icNegCutAdj_dot_zero_zero,
      icNegCutAdj_dot_plus_plus, icNegCutAdj_dot_minus_zero,
      icNegCutAdj_dot_zero_minus, icNegCutAdj_dot_minus_plus,
      icNegCutAdj_dot_plus_minus, icNegCutAdj_dot_zero_plus,
      icNegCutAdj_dot_plus_zero]
    ring
  rw [hM, hD]
  nlinarith [sq_nonneg (c 0), sq_nonneg (c 1)]

theorem icNegCut_trace :
    (normalizedLaplacian icNegCutAdj).trace = -3 := by
  rw [show (normalizedLaplacian icNegCutAdj).trace
      = ∑ i, normalizedLaplacian icNegCutAdj i i from rfl,
    Fin.sum_univ_three]
  simp [icNegCutAdj_normLap_entry, icNegCutAdj_deg, Real.sqrt_one,
    inv_one, mul_one]
  norm_num [icNegCutAdj, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons]

/-- **The exact pin: `λ₂ (L_sym) = 0`.** The three engine bounds
(`e₀ ≤ -5`, `e₁ ≤ 0`, `e₂ ≤ 2`) plus the trace `-3` force
`e₁ = -3 - e₀ - e₂ ≥ -3 + 5 - 2 = 0`. -/
theorem icNegCut_secondEval_eq_zero :
    secondEval (normalizedLaplacian icNegCutAdj)
      (normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric)
      (by decide) = 0 := by
  have hM := normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric
  have hsum3 : evals hM ⟨0, by norm_num⟩ + evals hM ⟨1, by norm_num⟩
      + evals hM ⟨2, by norm_num⟩ = -3 := by
    have ht := evals_sum_eq_trace hM
    rw [icNegCut_trace, Finset.sum_fin_eq_sum_range] at ht
    simp only [Fintype.card_fin] at ht
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at ht
    simp only [Nat.lt_succ_self, reduceDIte] at ht
    exact ht
  have h0 : evals hM ⟨0, by norm_num⟩ ≤ -5 := icNegCut_evals_zero_le
  have h1 : evals hM ⟨1, by norm_num⟩ ≤ 0 := icNegCut_evals_one_le
  have h2 : evals hM ⟨2, by norm_num⟩ ≤ 2 := icNegCut_evals_two_le
  have hsplit : evals hM ⟨1, by norm_num⟩
      = -3 - evals hM ⟨0, by norm_num⟩ - evals hM ⟨2, by norm_num⟩ := by
    linarith
  rw [show secondEval (normalizedLaplacian icNegCutAdj) hM (by decide)
      = evals hM ⟨1, by norm_num⟩ from rfl, hsplit]
  linarith

/-- The kernel characterization: every kernel vector is a multiple of
`(1, √2, 1)` (rows `0` and `2` force `x₀ = x₂`; row `1` then forces
`x₁ = √2 x₀`). -/
theorem icNegCut_ker_eq (x : Fin 3 → ℝ)
    (hx : normalizedLaplacian icNegCutAdj *ᵥ x = 0) :
    ∃ c : ℝ, x = c • (![1, Real.sqrt 2, 1] : Fin 3 → ℝ) := by
  have hentry := icNegCutAdj_normLap_entry
  have hrow : ∀ i : Fin 3,
      (∑ j, normalizedLaplacian icNegCutAdj i j * x j) = 0 := by
    intro i
    have hh := congrFun hx i
    simpa only [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply] using hh
  have e0 : -(2 : ℝ) * x 0 - (Real.sqrt 2)⁻¹ * x 1 + 3 * x 2 = 0 := by
    have hh := hrow 0
    simp only [hentry, Fin.sum_univ_three] at hh
    rw [icNegCutAdj_deg 0, icNegCutAdj_deg 1, icNegCutAdj_deg 2] at hh
    simp only [Real.sqrt_one, inv_one, mul_one, one_mul] at hh
    simp [icNegCutAdj, icNegCut_inv_sqrt_two_mul_sqrt_two] at hh
    linear_combination hh
  have e1 : -(Real.sqrt 2)⁻¹ * x 0 + x 1 - (Real.sqrt 2)⁻¹ * x 2 = 0 := by
    have hh := hrow 1
    simp only [hentry, Fin.sum_univ_three] at hh
    rw [icNegCutAdj_deg 0, icNegCutAdj_deg 1, icNegCutAdj_deg 2] at hh
    simp only [Real.sqrt_one, inv_one, mul_one, one_mul] at hh
    simp [icNegCutAdj, icNegCut_inv_sqrt_two_mul_sqrt_two] at hh
    linear_combination hh
  have e2 : 3 * x 0 - (Real.sqrt 2)⁻¹ * x 1 - 2 * x 2 = 0 := by
    have hh := hrow 2
    simp only [hentry, Fin.sum_univ_three] at hh
    rw [icNegCutAdj_deg 0, icNegCutAdj_deg 1, icNegCutAdj_deg 2] at hh
    simp only [Real.sqrt_one, inv_one, mul_one, one_mul] at hh
    simp [icNegCutAdj, icNegCut_inv_sqrt_two_mul_sqrt_two] at hh
    linear_combination hh
  have h5 : 5 * (x 0 - x 2) = 0 := by linear_combination e2 - e0
  have hx02 : x 0 = x 2 := by
    rcases mul_eq_zero.1 h5 with h | h
    · norm_num at h
    · linarith
  have hx1 : x 1 = (Real.sqrt 2)⁻¹ * (x 0 + x 2) := by linear_combination e1
  refine ⟨x 0, ?_⟩
  have hsum : x 0 + x 2 = 2 * x 0 := by rw [← hx02]; ring
  have hx1' : x 1 = Real.sqrt 2 * x 0 := by
    calc x 1 = (Real.sqrt 2)⁻¹ * (2 * x 0) := by rw [hx1, hsum]
      _ = ((Real.sqrt 2)⁻¹ * 2) * x 0 := by ring
      _ = (2 * (Real.sqrt 2)⁻¹) * x 0 := by ring
      _ = Real.sqrt 2 * x 0 := by rw [icNegCut_two_inv_sqrt_two]
  funext i
  fin_cases i
  · simp only [Pi.smul_apply, smul_eq_mul]
    simp
  · show x 1 = (x 0 • (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)) 1
    rw [hx1']
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one]
    simp
    ring
  · show x 2 = (x 0 • (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)) 2
    rw [← hx02]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_succ,
      Matrix.head_cons, Matrix.cons_val_zero]
    simp

/-- **The sweep vector is a nonzero constant** at the fixture: the
Fiedler vector lies in the one-dimensional `λ₂ = 0` eigenspace, and
`D⁻¹ᐟ² · (1, √2, 1) = (1, 1, 1)`. -/
theorem icNegCut_sweep_const :
    ∃ c : ℝ, c ≠ 0 ∧ fiedlerSweepVector icNegCutAdj icNegCutAdj_symmetric
        (by decide) = c • (1 : Fin 3 → ℝ) := by
  have hzero : normalizedLaplacian icNegCutAdj
      *ᵥ fiedlerVectorNormalized icNegCutAdj icNegCutAdj_symmetric
        (by decide) = 0 := by
    have h := fiedlerVectorNormalized_eigen icNegCutAdj icNegCutAdj_symmetric
      (by decide)
    rw [icNegCut_secondEval_eq_zero] at h
    rw [zero_smul] at h
    exact h
  obtain ⟨c, hc⟩ := icNegCut_ker_eq _ hzero
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact fiedlerVectorNormalized_ne_zero icNegCutAdj icNegCutAdj_symmetric
      (by decide) hc
  refine ⟨c, hc0, ?_⟩
  have h1 : degreeInvSqrt icNegCutAdj *ᵥ (![1, Real.sqrt 2, 1] : Fin 3 → ℝ)
      = (1 : Fin 3 → ℝ) := by
    funext i
    rw [degreeInvSqrt_mulVec_apply, icNegCutAdj_deg]
    fin_cases i
    · simp [Real.sqrt_one]
    · simp [Matrix.cons_val_one,
        icNegCut_inv_sqrt_two_mul_sqrt_two]
    · simp [Real.sqrt_one, Matrix.cons_val_succ, Matrix.head_cons,
        Matrix.cons_val_zero]
  rw [fiedlerSweepVector, hc, Matrix.mulVec_smul_assoc, h1]

/-- **Fence (Fiedler capstone, `hnn`)**: at the connected negative-cut
fixture `λ₂ (L_sym) = 0` and the one-dimensional `λ₂`-eigenspace is
spanned by `(1, √2, 1)`, so the sweep vector is a *nonzero constant*
— its superlevel/sublevel family contains no nonempty proper member
at all, and the nonnegativity-dropped conclusion fails on the shape
clauses. -/
theorem icf_fiedler_hnn_fence_QA :
    ¬ (∃ S : Finset (Fin 3), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤
          fiedlerSweepVector icNegCutAdj icNegCutAdj_symmetric
            (by decide) i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔
          fiedlerSweepVector icNegCutAdj icNegCutAdj_symmetric
            (by decide) i ≤ t)) ∧
      conductance icNegCutAdj S ^ 2
        ≤ 2 * secondEval (normalizedLaplacian icNegCutAdj)
            (normalizedLaplacian_symmetric icNegCutAdj icNegCutAdj_symmetric)
            (by decide)) := by
  obtain ⟨c, hc0, hsw⟩ := icNegCut_sweep_const
  rintro ⟨S, hSne, hSc, hlev, -⟩
  refine icf_no_proper_level_of_const c S hSne hSc ?_
  rcases hlev with ⟨t, ht⟩ | ⟨t, ht⟩
  · refine Or.inl ⟨t, fun i => ?_⟩
    have hh := ht i
    rw [hsw] at hh
    simpa using hh
  · refine Or.inr ⟨t, fun i => ?_⟩
    have hh := ht i
    rw [hsw] at hh
    simpa using hh

theorem icf_fiedler_hnn_isolation_QA :
    icNegCutAdj.IsSymm
      ∧ (∀ i, 0 < deg icNegCutAdj i)
      ∧ 2 ≤ Fintype.card (Fin 3)
      ∧ (supportGraph icNegCutAdj icNegCutAdj_symmetric).Connected
      ∧ ¬ (∀ i j, 0 ≤ icNegCutAdj i j) :=
  icf_cheeger_pos_hnn_isolation_QA

/-! ### The attainment theorem's `hcard` clause -/

/-- The one-vertex fixture: nonnegative by construction. -/
def icOneAdj : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => 0

theorem icOneAdj_nonneg : ∀ i j, 0 ≤ icOneAdj i j := by
  intro i j
  rfl

/-- **Fence (attainment, `hcard`)**: on a one-element type no nonempty
proper subset exists, so the cardinality-dropped conclusion's
existential fails outright — the `2 ≤ card V` guard is what keeps the
attainment statement's search space nonempty. -/
theorem icf_attain_hcard_fence_QA :
    ¬ (∃ S : Finset (Fin 1), S.Nonempty ∧ Sᶜ.Nonempty ∧
        conductance icOneAdj S = cheegerConstant icOneAdj) := by
  rintro ⟨S, hSne, hSc, -⟩
  obtain ⟨i, hi⟩ := hSne
  fin_cases i
  have hU : S = Finset.univ :=
    Finset.eq_univ_iff_forall.2 fun j => by
      fin_cases j
      simpa using hi
  rw [hU, Finset.compl_univ] at hSc
  exact absurd hSc (by simp)

theorem icf_attain_hcard_isolation_QA :
    (∀ i j, 0 ≤ icOneAdj i j) ∧ ¬ (2 ≤ Fintype.card (Fin 1)) :=
  ⟨icOneAdj_nonneg, by norm_num⟩

end IrregularFences

end SpectralGraphTheory.QA