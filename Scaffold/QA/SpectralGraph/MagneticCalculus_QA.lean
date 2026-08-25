/-
  MagneticCalculus_QA.lean

  Purpose
  -------
  QA lemmas for the magnetic heat propagator — the first complex
  consumer of the Hermitian functional-calculus bridge
  (`proposals/hermitian-calculus-consumer-magnetic.md`, 2026-08-25) —
  exercising `GraphTheory.FunctionalCalculus`'s complex layer
  (`magneticHeat` and its interfaces) on a genuinely complex,
  genuinely fluxed fixture, per the proposal's QA plan: one small
  directed-phase fixture with a hand computation, checked by two
  independent routes. Sections:

  - **A (the operator pinned):** the flux pair `K₂` at antisymmetric
    phase `π/2` — `M = !![1, -I; I, 1]`, genuinely complex Hermitian —
    with the symmetrized degree, the conjugate-pair off-diagonals,
    and Hermiticity verified on directed-flux input.

  - **B (the eigenvector equations, raw):** the balanced potential
    `![I, 1]` in the kernel and the frustrated mode `![I, -1]` at
    eigenvalue `2`, by raw arithmetic; the kernel cross-checked
    against the delivered gauge characterization by two routes (the
    iff theorem against the raw energy collapse).

  - **C (the propagator's action and closed form, two routes):** the
    calculus route derives the actions through the public eigen-action
    theorem; the hand-derived closed form
    `½ !![1+q, I(1-q); -I(1-q), 1+q]` at `q = e^{-2t}` is verified by
    raw matrix arithmetic (route 2, no calculus anywhere); the
    reconciliation `magneticHeat = closed` joins them through the
    spanning-recovery helper (actions on a spanning pair determine the
    matrix).

  - **D (pins and fences):** time zero (public theorem + raw
    cross-check at `q = 1`), the semigroup law, Hermiticity of the
    propagator, and the diffusion fence — `magneticHeat … 1 ≠ 1`
    because `e^{-2} < 1` forces the off-diagonal entry nonzero: phase
    frustration provably moves mass, refuting any constant-collapse
    reading.

  - **E (the zero-phase join with the real shelf):** at vanishing flux
    the magnetic propagator IS the complexification of the delivered
    real `heatKernel` — Mathlib's `cfc` at the complexified operator
    against `Heat.lean`'s exponential series at the real operator, two
    independent proof technologies agreeing on one operator through
    the spanning family of the classical eigenvectors.

  Fixtures are `Fin 2` with phase `π/2` so `e^{iθ} = I` exactly; all
  proofs are raw computations, single-theorem instantiations, or the
  two-route reconciliations above; no `sorry`, no `admit`, no new
  assumptions.
-/
import Scaffold.Mathlib.GraphTheory.FunctionalCalculus
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.LinearCombination

open scoped BigOperators Matrix ComplexConjugate

namespace SpectralGraphTheory.QA

/-! ### Fixtures -/

/-- The symmetric pair (`K₂` adjacency). -/
def magC_A : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- Antisymmetric `π/2`-flux pair on the symmetric edge. -/
noncomputable def magC_Θ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, Real.pi / 2; -(Real.pi / 2), 0]

private theorem magC_exp_half_pi :
    Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  rw [mul_comm, Complex.exp_mul_I]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re]

private theorem magC_exp_neg_half_pi :
    Complex.exp (Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ)) = -Complex.I := by
  have h : Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ)
      = -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h, Complex.exp_neg, magC_exp_half_pi]
  norm_num

private theorem magC_exp_half_pi_div :
    Complex.exp (Complex.I * ((Real.pi : ℂ) / 2)) = Complex.I := by
  rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) from by
      push_cast [Complex.ofReal_div]
      rfl]
  exact magC_exp_half_pi

private theorem magC_exp_neg_half_pi_div :
    Complex.exp (-(Complex.I * ((Real.pi : ℂ) / 2))) = -Complex.I := by
  rw [Complex.exp_neg, magC_exp_half_pi_div]
  norm_num

/-! ### The operator pinned -/

theorem magC_symDeg (u : Fin 2) : symDeg magC_A u = 1 := by
  fin_cases u <;>
    norm_num [symDeg, magC_A, outDeg, inDeg, Fin.sum_univ_two]

theorem magC_M_01 : magneticLaplacian magC_A magC_Θ 0 1 = -Complex.I := by
  have hw01 : magneticMatrix magC_A magC_Θ 0 1 = Complex.I := by
    show (magC_A 0 1 : ℂ) * Complex.exp (Complex.I * (magC_Θ 0 1 : ℂ))
      = Complex.I
    rw [show (magC_A 0 1 : ℝ) = 1 from rfl,
      show (magC_Θ 0 1 : ℝ) = Real.pi / 2 from rfl, magC_exp_half_pi]
    push_cast
    ring
  have hw10 : magneticMatrix magC_A magC_Θ 1 0 = -Complex.I := by
    show (magC_A 1 0 : ℂ) * Complex.exp (Complex.I * (magC_Θ 1 0 : ℂ))
      = -Complex.I
    rw [show (magC_A 1 0 : ℝ) = 1 from rfl,
      show (magC_Θ 1 0 : ℝ) = -(Real.pi / 2) from rfl, magC_exp_neg_half_pi]
    push_cast
    ring
  have hc10 : star (magneticMatrix magC_A magC_Θ 1 0) = Complex.I := by
    rw [hw10, Complex.star_def]
    exact Complex.conj_neg_I
  show ((Matrix.diagonal (fun w => (symDeg magC_A w : ℂ))
        - (1 / 2 : ℂ) • (magneticMatrix magC_A magC_Θ
            + (magneticMatrix magC_A magC_Θ)ᴴ)) 0 1) = _
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.conjTranspose_apply,
    Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    hw01, hc10]
  ring

theorem magC_M_10 : magneticLaplacian magC_A magC_Θ 1 0 = Complex.I := by
  have hw01 : magneticMatrix magC_A magC_Θ 0 1 = Complex.I := by
    show (magC_A 0 1 : ℂ) * Complex.exp (Complex.I * (magC_Θ 0 1 : ℂ))
      = Complex.I
    rw [show (magC_A 0 1 : ℝ) = 1 from rfl,
      show (magC_Θ 0 1 : ℝ) = Real.pi / 2 from rfl, magC_exp_half_pi]
    push_cast
    ring
  have hw10 : magneticMatrix magC_A magC_Θ 1 0 = -Complex.I := by
    show (magC_A 1 0 : ℂ) * Complex.exp (Complex.I * (magC_Θ 1 0 : ℂ))
      = -Complex.I
    rw [show (magC_A 1 0 : ℝ) = 1 from rfl,
      show (magC_Θ 1 0 : ℝ) = -(Real.pi / 2) from rfl, magC_exp_neg_half_pi]
    push_cast
    ring
  have hc01 : star (magneticMatrix magC_A magC_Θ 0 1) = -Complex.I := by
    rw [hw01, Complex.star_def]
    exact Complex.conj_I
  show ((Matrix.diagonal (fun w => (symDeg magC_A w : ℂ))
        - (1 / 2 : ℂ) • (magneticMatrix magC_A magC_Θ
            + (magneticMatrix magC_A magC_Θ)ᴴ)) 1 0) = _
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.conjTranspose_apply,
    Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
    hw10, hc01]
  ring

theorem magC_M_diag (u : Fin 2) :
    magneticLaplacian magC_A magC_Θ u u = 1 := by
  have hz : ∀ w : Fin 2, magC_Θ w w = 0 := by
    intro w; fin_cases w <;> rfl
  have hself : ∀ w : Fin 2, magneticMatrix magC_A magC_Θ w w
      = (magC_A w w : ℂ) := by
    intro w
    show (magC_A w w : ℂ) * Complex.exp (Complex.I * (magC_Θ w w : ℂ)) = _
    rw [hz w]
    push_cast
    simp
  show ((Matrix.diagonal (fun w => (symDeg magC_A w : ℂ))
        - (1 / 2 : ℂ) • (magneticMatrix magC_A magC_Θ
            + (magneticMatrix magC_A magC_Θ)ᴴ)) u u) = _
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    hself u, Complex.star_def, Complex.conj_ofReal, magC_symDeg]
  fin_cases u <;> norm_num [magC_A]

/-- Hermitian on the directed-flux fixture (the hypothesis-free
theorem on genuinely complex input). -/
theorem magC_M_herm :
    (magneticLaplacian magC_A magC_Θ)ᴴ = magneticLaplacian magC_A magC_Θ :=
  (magneticLaplacian_isHermitian magC_A magC_Θ).eq

/-! ### The eigenvector equations, raw -/

/-- The balanced-potential vector: in the kernel of the flux pair. -/
def magC_v0 : Fin 2 → ℂ := ![Complex.I, 1]

/-- The frustrated vector: eigenvalue `2` on the flux pair. -/
def magC_v1 : Fin 2 → ℂ := ![Complex.I, -1]

theorem magC_M_mulVec_v0 : magneticLaplacian magC_A magC_Θ *ᵥ magC_v0 = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, magC_M_01, magC_M_10, magC_M_diag,
      magC_v0]

theorem magC_M_mulVec_v1 :
    magneticLaplacian magC_A magC_Θ *ᵥ magC_v1 = (2 : ℂ) • magC_v1 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, magC_M_01, magC_M_10, magC_M_diag,
      magC_v1, Pi.smul_apply, smul_eq_mul]
  · ring
  · ring

/-- The kernel vector cross-checked against the delivered gauge
characterization (route 1 — the iff theorem at the verified
balanced-potential condition). -/
theorem magC_gauge_v0_route_theorem :
    hermQuadForm (magneticLaplacian magC_A magC_Θ) magC_v0 = 0 := by
  refine (magneticQuadForm_eq_zero_iff magC_A magC_Θ magC_v0 ?_).2 ?_
  · intro u v
    fin_cases u <;> fin_cases v <;> simp [magC_A]
  · intro u v _
    fin_cases u <;> fin_cases v <;>
      simp [magC_v0, magC_Θ, magC_exp_half_pi_div,
        magC_exp_neg_half_pi_div]

/-- Route 2 to the same kernel membership: the raw eigenvector
equation collapses the energy sum at the zero action. -/
theorem magC_gauge_v0_route_raw :
    hermQuadForm (magneticLaplacian magC_A magC_Θ) magC_v0 = 0 := by
  rw [hermQuadForm, magC_M_mulVec_v0]
  simp

/-! ### The spanning recovery helper -/

/-- Two complex `2×2` matrices agreeing on a spanning pair are equal:
actions determine the matrix (entries are actions on the coordinate
units, each a linear combination of the pair). The explicit
combination certificate is a hypothesis, so the helper serves any
spanning pair. -/
private theorem magC2_eq_of_action {v0 v1 : Fin 2 → ℂ}
    (hcomb : ∀ x : Fin 2 → ℂ, ∃ a b : ℂ, x = a • v0 + b • v1)
    {M N : Matrix (Fin 2) (Fin 2) ℂ}
    (h0 : M *ᵥ v0 = N *ᵥ v0) (h1 : M *ᵥ v1 = N *ᵥ v1) : M = N := by
  have key : ∀ x : Fin 2 → ℂ, M *ᵥ x = N *ᵥ x := by
    intro x
    obtain ⟨a, b, hx⟩ := hcomb x
    rw [hx, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h0, h1,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  ext i j
  have h := key (Pi.single j (1 : ℂ))
  simpa [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply] using congrFun h i

/-- The flux-pair eigenvectors span: explicit coefficients. -/
private theorem magC_pair_comb (x : Fin 2 → ℂ) :
    ∃ a b : ℂ, x = a • magC_v0 + b • magC_v1 :=
  ⟨x 0 / (2 * Complex.I) + x 1 / 2, x 0 / (2 * Complex.I) - x 1 / 2, by
    funext k
    fin_cases k <;>
      simp only [magC_v0, magC_v1, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    · field_simp
      ring
    · field_simp
      ring⟩

/-! ### The propagator's action, two routes -/

/-- The decay factor as a complex number: `q t = e^{-2t}`. -/
noncomputable def magC_q (t : ℝ) : ℂ := ((Real.exp (-(2 * t)) : ℝ) : ℂ)

/-- Route 1 (calculus): the balanced potential is flux-invariant —
the kernel mode is preserved under the propagator, at every time. -/
theorem magC_heat_v0 (t : ℝ) :
    magneticHeat magC_A magC_Θ t *ᵥ magC_v0 = magC_v0 := by
  have he : magneticLaplacian magC_A magC_Θ *ᵥ magC_v0
      = ((0 : ℝ) : ℂ) • magC_v0 := by
    rw [Complex.ofReal_zero, zero_smul]
    exact magC_M_mulVec_v0
  rw [magneticHeat_mulVec_of_eigen magC_A magC_Θ he t,
    show -(t * 0) = (0 : ℝ) from by rw [mul_zero, neg_zero],
    Real.exp_zero, Complex.ofReal_one, one_smul]

/-- Route 1 (calculus): the frustrated mode decays at rate `e^{-2t}`. -/
theorem magC_heat_v1 (t : ℝ) :
    magneticHeat magC_A magC_Θ t *ᵥ magC_v1 = magC_q t • magC_v1 := by
  have he : magneticLaplacian magC_A magC_Θ *ᵥ magC_v1
      = ((2 : ℝ) : ℂ) • magC_v1 := by
    rw [Complex.ofReal_ofNat]
    exact magC_M_mulVec_v1
  rw [magneticHeat_mulVec_of_eigen magC_A magC_Θ he t,
    show -(t * 2) = -(2 * t) from by ring]
  rfl

/-! ### The closed form, two routes -/

/-- The hand-derived closed form of the flux-pair propagator:
`½ !![1+q, I(1-q); -I(1-q), 1+q]` — the kernel projector plus the
decaying frustrated-mode projector, at `q = e^{-2t}`. -/
noncomputable def magC_closed (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + magC_q t) / 2, Complex.I * (1 - magC_q t) / 2;
     -Complex.I * (1 - magC_q t) / 2, (1 + magC_q t) / 2]

/-- Route 2 (raw): the closed form's action on the kernel mode, by
pure matrix arithmetic — no calculus anywhere. -/
theorem magC_closed_mulVec_v0 (t : ℝ) :
    magC_closed t *ᵥ magC_v0 = magC_v0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, magC_closed, magC_v0, mul_one]
  · ring
  · linear_combination (norm := ring_nf)
      (-(1 - magC_q t) / 2) * Complex.I_mul_I

/-- Route 2 (raw): the closed form's action on the frustrated mode. -/
theorem magC_closed_mulVec_v1 (t : ℝ) :
    magC_closed t *ᵥ magC_v1 = magC_q t • magC_v1 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, magC_closed, magC_v1,
      Pi.smul_apply, smul_eq_mul]
  · ring
  · linear_combination (norm := ring_nf)
      (-(1 - magC_q t) / 2) * Complex.I_mul_I

/-- **The reconciliation**: the calculus-built propagator IS the
hand-derived closed form — derived on the calculus route (the two
eigen-actions via the public action theorem, then the spanning
recovery), with the closed form's own actions independently verified
by raw arithmetic above. A wrong calculus specialization or a wrong
action theorem breaks the equality loudly. -/
theorem magC_heat_closed (t : ℝ) :
    magneticHeat magC_A magC_Θ t = magC_closed t := by
  refine magC2_eq_of_action magC_pair_comb ?_ ?_
  · rw [magC_heat_v0, magC_closed_mulVec_v0]
  · rw [magC_heat_v1, magC_closed_mulVec_v1]

/-! ### Pins, fences, and the join with the real shelf -/

/-- Time zero: the propagator is the identity (public theorem, pinned
on the fixture). -/
theorem magC_heat_zero : magneticHeat magC_A magC_Θ 0 = 1 :=
  magneticHeat_zero magC_A magC_Θ

/-- The raw cross-check of time zero: the closed form at `q = 1`. -/
theorem magC_closed_zero : magC_closed 0 = 1 := by
  have hq : magC_q 0 = 1 := by simp [magC_q]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [magC_closed, hq, Matrix.one_apply]

/-- The semigroup law on the fixture (public theorem, pinned). -/
theorem magC_heat_mul (s t : ℝ) :
    magneticHeat magC_A magC_Θ s * magneticHeat magC_A magC_Θ t
      = magneticHeat magC_A magC_Θ (s + t) :=
  magneticHeat_mul_magneticHeat magC_A magC_Θ s t

/-- The closed form is Hermitian (the conjugate-pair off-diagonals at
a real decay factor). -/
private theorem magC_q_conj (t : ℝ) : conj (magC_q t) = magC_q t := by
  show conj (((Real.exp (-(2 * t)) : ℝ) : ℂ)) = _
  rw [Complex.conj_ofReal]
  rfl

private theorem magC_closed_herm (t : ℝ) : (magC_closed t).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [magC_closed, magC_q_conj, Complex.conj_I, Complex.star_def,
      Complex.conj_ofReal, map_div₀, map_mul, map_add, map_sub, map_neg]

/-- The propagator is Hermitian on the fixture. -/
theorem magC_heat_herm (t : ℝ) :
    (magneticHeat magC_A magC_Θ t)ᴴ = magneticHeat magC_A magC_Θ t := by
  rw [magC_heat_closed t]
  exact magC_closed_herm t |>.eq

/-- The diffusion fence: at `t = 1` the propagator is provably not
the identity — the frustrated mode decays (`e^{-2} < 1` since
`-2 < 0`), so the off-diagonal entry `I(1-q)/2 ≠ 0`. -/
theorem magC_heat_one_ne_one : magneticHeat magC_A magC_Θ 1 ≠ 1 := by
  have hq : (Real.exp (-(2 : ℝ))) < 1 := by
    have h2 : Real.exp (-(2 : ℝ)) < Real.exp (0 : ℝ) :=
      Real.exp_lt_exp.2 (by norm_num)
    rwa [Real.exp_zero] at h2
  intro h
  have hentry : magC_closed 1 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
    have hc : magneticHeat magC_A magC_Θ 1 = magC_closed 1 := magC_heat_closed 1
    rw [← hc, h]
  have hR : (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
    simp [Matrix.one_apply]
  rw [hR] at hentry
  have hL : magC_closed 1 0 1
      = Complex.I * (1 - ((Real.exp (-(2 : ℝ)) : ℝ) : ℂ)) / 2 := by
    simp [magC_closed, magC_q]
  rw [hL] at hentry
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hsub : ((1 : ℝ) : ℂ) - ((Real.exp (-(2 : ℝ)) : ℝ) : ℂ) = 0 := by
    rw [div_eq_zero_iff] at hentry
    rcases hentry with hh | hh
    · rcases mul_eq_zero.1 hh with hh' | hh'
      · exact absurd hh' hI
      · rw [Complex.ofReal_one]
        exact sub_eq_zero.2 (sub_eq_zero.1 hh')
    · exact absurd hh (by norm_num)
  rw [← Complex.ofReal_sub, Complex.ofReal_eq_zero] at hsub
  linarith

/-! ### The zero-phase join with the real heat semigroup -/

/-- The complexification of a real matrix, entrywise. -/
noncomputable def magC_coe (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => ((M i j : ℝ) : ℂ)

/-- The complexification of a real vector. -/
noncomputable def magC_cw (w : Fin 2 → ℝ) : Fin 2 → ℂ :=
  fun i => ((w i : ℝ) : ℂ)

private theorem magC_sym : magC_A.IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [magC_A]

/-- Complexified action agreement: the complexified matrix acts on the
complexified vector as the complexification of the real action. -/
private theorem magC_coe_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ)
    (w : Fin 2 → ℝ) :
    magC_coe M *ᵥ magC_cw w = magC_cw (M *ᵥ w) := by
  funext i
  simp [magC_coe, magC_cw, Matrix.mulVec, Matrix.dotProduct,
    Complex.ofReal_sum, ← Complex.ofReal_mul]

/-- The zero-phase magnetic operator is the complexified classical
Laplacian on the fixture. -/
private theorem magC_M_zero :
    magneticLaplacian magC_A 0 = magC_coe (laplacian magC_A) := by
  ext i j
  rw [magneticLaplacian_zero_phase_apply_of_isSymm magC_sym]
  rfl

/-- The real classical eigenvector equations on `K₂`, raw. -/
theorem magC_L_mulVec_w0 : laplacian magC_A *ᵥ ![1, 1] = 0 := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, magC_A, Matrix.mulVec,
      Matrix.dotProduct]

theorem magC_L_mulVec_w1 :
    laplacian magC_A *ᵥ ![1, -1] = (2 : ℝ) • ![1, -1] := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, magC_A, Matrix.mulVec,
      Matrix.dotProduct, Pi.smul_apply, smul_eq_mul] <;>
    norm_num

/-- The real heat kernel acts at eigenvalues on every eigenvector —
the series engine (`exp_mulVec_eq_smul_of_mulVec_eq_smul`), the
independent proof technology this join is reconciling with the
calculus. -/
private theorem magC_heat_action (t : ℝ) (w : Fin 2 → ℝ) (μ : ℝ)
    (hw : laplacian magC_A *ᵥ w = μ • w) :
    heatKernel magC_A t *ᵥ w = Real.exp (-(t * μ)) • w := by
  rw [heatKernel]
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, hw, smul_smul, neg_smul]

/-- **The zero-phase join**: at vanishing flux the magnetic propagator
IS the complexification of the delivered real heat semigroup — two
independent proof technologies (Mathlib's `cfc` at the complexified
operator against `Heat.lean`'s exponential series at the real
operator) agreeing on one operator, joined through the spanning
family of the classical eigenvectors. -/
theorem magC_zero_phase_join (t : ℝ) :
    magneticHeat magC_A 0 t = magC_coe (heatKernel magC_A t) := by
  have hcomb : ∀ x : Fin 2 → ℂ,
      ∃ a b : ℂ, x = a • (magC_cw ![1, 1]) + b • (magC_cw ![1, -1]) := by
    intro x
    refine ⟨(x 0 + x 1) / 2, (x 0 - x 1) / 2, ?_⟩
    funext k
    fin_cases k <;>
      simp only [magC_cw, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    · field_simp
    · field_simp
      ring
  refine magC2_eq_of_action hcomb ?_ ?_
  · -- the kernel mode: both propagators act as the identity
    have hm0 : magneticLaplacian magC_A 0 *ᵥ (magC_cw ![1, 1])
        = ((0 : ℝ) : ℂ) • (magC_cw ![1, 1]) := by
      rw [magC_M_zero, magC_coe_mulVec, magC_L_mulVec_w0,
        Complex.ofReal_zero, zero_smul]
      rfl
    have hw0' : laplacian magC_A *ᵥ ![1, 1]
        = (0 : ℝ) • ![1, 1] := by
      rw [zero_smul]
      exact magC_L_mulVec_w0
    rw [magneticHeat_mulVec_of_eigen magC_A 0 hm0 t, magC_coe_mulVec,
      magC_heat_action t ![1, 1] 0 hw0',
      show -(t * 0) = (0 : ℝ) from by rw [mul_zero, neg_zero],
      Real.exp_zero, Complex.ofReal_one, one_smul, one_smul]
  · -- the frustrated mode: both act as e^{-2t}
    have hm1 : magneticLaplacian magC_A 0 *ᵥ (magC_cw ![1, -1])
        = ((2 : ℝ) : ℂ) • (magC_cw ![1, -1]) := by
      rw [magC_M_zero, magC_coe_mulVec, magC_L_mulVec_w1]
      funext i
      simp only [magC_cw, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
        Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.head_cons, Matrix.cons_val_one, Complex.ofReal_mul]
    rw [magneticHeat_mulVec_of_eigen magC_A 0 hm1 t,
      show -(t * 2) = -(2 * t) from by ring,
      magC_coe_mulVec, magC_heat_action t ![1, -1] 2 magC_L_mulVec_w1]
    funext i
    simp only [magC_cw, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Complex.ofReal_mul]
    push_cast
    ring_nf

end SpectralGraphTheory.QA
