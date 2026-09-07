/-
  Magnetic_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Magnetic` (the
  magnetic-Laplacian first slice, `proposals/magnetic-laplacian.md`),
  the shelf's first complex-valued object. Four sections per the
  proposal's QA plan:

  - **A (positive/asymmetric):** the hypothesis-free content
    instantiated on genuinely asymmetric input with genuinely complex
    phases — the raw phase-weighted entries `W 0 1 = -2` and
    `W 1 0 = I`, the operator's off-diagonal entries pinned raw
    (`L 0 1 = 1 + I/2`, `L 1 0 = 1 - I/2`), Hermitian verified
    entrywise, the energy identity pinned numerically at a complex
    test vector (both routes `5`), the zero-phase agreement with the
    complexified classical Laplacian, and the symmetric-cone
    single-`W` form at a `π`-flux pair.

  - **B (frustration vs consistency):** the gauge characterization's
    content. The triangle with one `π`-flux edge is *frustrated*: the
    gauge condition forces `x = 0`, so the form is positive definite
    (spectral localization of flux at form level — no eigenvalue
    machinery anywhere). Against it, the same flux on a single edge
    (`K₂`) is *consistent*: the antipodal phase potential survives in
    the kernel, verified through the iff's reverse direction and
    cross-checked by the raw vanishing energy.

  - **C (the classical bridge):** at zero phase the constant complex
    vector lies in the kernel, and the antipodal vector is provably
    *outside* it (energy exactly `2`): the flux is what moved the
    kernel.

  - **D (the nonnegativity fence):** symmetric *signed* input refutes
    PSD in proved form (`-1 < 0`) — the hypothesis-free conclusion is
    false, so `hA : 0 ≤ A` is exercised, not decorated. This is the
    signed-graph surface the fence marks.

  - **E (the structural pins):** first genuine consumption of the six
    structural theorems the compiler-derived consumption census found
    inert (never referenced by any QA proof term — the sections above
    pin the form-level facts *beside* them). Both directions of the
    action-level kernel characterization, the PSD, the real-valuedness
    promotion, the row-algebra reverse direction, the kernel-to-form
    helper, and the unit-phase pairing — including the directed
    frustration witness (`π` vs `π/2` on the asymmetric fixture forces
    the trivial kernel) and the classical-join cross-route
    (`proposals/magnetic-structural-pins.md`).

  Fixtures are `Fin 2`/`Fin 3` with phases from `{0, π/2, π}` so
  `e^{iθ} ∈ {1, I, -1}` exactly. Matrix entries evaluate by `rfl`
  (the `Directed_QA` entry-table pattern); all proofs are raw
  computations or single-theorem instantiations; no `sorry`, no
  `admit`, no new assumptions.
-/
import Scaffold.Mathlib.GraphTheory.Magnetic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.LinearCombination

open scoped BigOperators Matrix ComplexConjugate

namespace SpectralGraphTheory.QA

/-! ### Fixtures and raw entry tables -/

/-- Asymmetric two-vertex fixture: arc 0→1 of weight 2, arc 1→0 of
weight 1. Genuinely directed input for the hypothesis-free theorems. -/
noncomputable def magA : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 2; 1, 0]

/-- Phases: `π` on 0→1, `π/2` on 1→0 — asymmetric, no zero row. -/
noncomputable def magTheta : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, Real.pi; Real.pi / 2, 0]

/-- Symmetric edge weights (`K₂`). -/
def magSym : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- Antisymmetric `π`-flux pair on the symmetric edge. -/
noncomputable def magThetaPi : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, Real.pi; -Real.pi, 0]

/-- Zero phases. -/
def magThetaZero : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 0, 0]

/-- The symmetric triangle (off-diagonal ones). -/
def magTri : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 1; 1, 0, 1; 1, 1, 0]

/-- Antisymmetric triangle phases with a single `π` edge: `Θ 0 1 = π`,
`Θ 1 0 = -π`, all other pairs at phase `0`. -/
noncomputable def magThetaTri : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, Real.pi, 0; -Real.pi, 0, 0; 0, 0, 0]

/-- Signed symmetric fixture: one negative edge, symmetry intact. -/
def magSigned : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; -1, 0]

/-! ### Exact phase evaluations -/

private theorem magExp_eq (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ))
      = ((Real.cos t : ℂ)) + ((Real.sin t : ℂ)) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private theorem magExp_pi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
  rw [magExp_eq]
  norm_num [Real.cos_pi, Real.sin_pi]

private theorem magExp_neg_pi :
    Complex.exp (Complex.I * ((-Real.pi : ℝ) : ℂ)) = -1 := by
  rw [magExp_eq]
  norm_num [Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]

private theorem magExp_half_pi :
    Complex.exp (Complex.I * (((Real.pi : ℂ) / 2))) = Complex.I := by
  have hco : Complex.exp (Complex.I * (((Real.pi / 2 : ℝ) : ℂ)))
      = ((Real.cos (Real.pi / 2) : ℂ)) + ((Real.sin (Real.pi / 2) : ℂ)) * Complex.I :=
    magExp_eq (Real.pi / 2)
  have hd : (((Real.pi : ℂ) / 2)) = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_div]
    rfl
  rw [hd, hco]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]

private theorem magExp_neg_pi_pushed :
    Complex.exp (-(Complex.I * ((Real.pi : ℂ)))) = -1 := by
  rw [Complex.exp_neg, magExp_pi]
  norm_num

private theorem magExp_half_pi_raw :
    Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  rw [show ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi : ℂ) / 2) from by
      push_cast [Complex.ofReal_div]
      rfl]
  exact magExp_half_pi

/-! ### Section A: positive/asymmetric witnesses -/

/-- Symmetrized degrees of the asymmetric fixture: both `3/2`. -/
theorem magA_symDeg : symDeg magA 0 = 3 / 2 ∧ symDeg magA 1 = 3 / 2 := by
  refine ⟨by norm_num [symDeg, magA, outDeg, inDeg, Fin.sum_univ_two], ?_⟩
  norm_num [symDeg, magA, outDeg, inDeg, Fin.sum_univ_two]

/-- The raw phase-weighted entries on the asymmetric fixture:
`W 0 1 = 2·e^{iπ} = -2` and `W 1 0 = 1·e^{iπ/2} = I`. -/
theorem magW_entries :
    magneticMatrix magA magTheta 0 1 = -2 ∧ magneticMatrix magA magTheta 1 0 = Complex.I := by
  constructor
  · show (magA 0 1 : ℂ) * Complex.exp (Complex.I * (magTheta 0 1 : ℂ)) = -2
    have h1 : (magA 0 1 : ℝ) = 2 := rfl
    have h2 : (magTheta 0 1 : ℝ) = Real.pi := rfl
    rw [h1, h2, magExp_pi]
    push_cast
    ring
  · show (magA 1 0 : ℂ) * Complex.exp (Complex.I * (magTheta 1 0 : ℂ)) = Complex.I
    have h1 : (magA 1 0 : ℝ) = 1 := rfl
    have h2 : (magTheta 1 0 : ℝ) = Real.pi / 2 := rfl
    rw [h1, h2, magExp_half_pi_raw]
    push_cast
    ring

/-- The off-diagonal entries of the magnetic Laplacian on the
asymmetric flux fixture, computed raw: `L 0 1 = 1 + I/2` and
`L 1 0 = 1 - I/2` — genuinely complex, conjugates of each other. -/
theorem magL_entries :
    magneticLaplacian magA magTheta 0 1 = 1 + Complex.I / 2
      ∧ magneticLaplacian magA magTheta 1 0 = 1 - Complex.I / 2 := by
  obtain ⟨hw01, hw10⟩ := magW_entries
  have hc10 : star (magneticMatrix magA magTheta 1 0) = -Complex.I := by
    rw [hw10, Complex.star_def]
    exact Complex.conj_I
  have hc01 : star (magneticMatrix magA magTheta 0 1) = -2 := by
    rw [hw01, Complex.star_def]
    norm_num [Complex.conj_ofNat]
  constructor
  · show ((Matrix.diagonal (fun w => (symDeg magA w : ℂ))
        - (1 / 2 : ℂ) • (magneticMatrix magA magTheta
            + (magneticMatrix magA magTheta)ᴴ)) 0 1) = _
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      hw01, hc10]
    ring
  · show ((Matrix.diagonal (fun w => (symDeg magA w : ℂ))
        - (1 / 2 : ℂ) • (magneticMatrix magA magTheta
            + (magneticMatrix magA magTheta)ᴴ)) 1 0) = _
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
      hw10, hc01]
    ring

/-- Hermitian on the asymmetric flux fixture — the hypothesis-free
theorem's content on genuinely directed input; the raw entry-level
evidence is the conjugate pair of `magL_entries` (`1 + I/2` and
`1 - I/2`). -/
theorem magHermitian_asymmetric :
    (magneticLaplacian magA magTheta)ᴴ = magneticLaplacian magA magTheta :=
  (magneticLaplacian_isHermitian magA magTheta).eq

/-- The energy identity instantiated at the test vector `![1, 1]` on
the asymmetric flux fixture, with the value pinned raw: both the
theorem route and the raw edge-energy sum give `5`
(`½[2·|1-(-1)|² + 1·|1-I|²] = ½[8+2]`). -/
theorem magEnergy_pin :
    hermQuadForm (magneticLaplacian magA magTheta) ![1, 1] = 5 := by
  rw [magnetic_energy]
  norm_num [magA, magTheta, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, magExp_pi, magExp_half_pi, Complex.normSq_apply]

theorem magSym_isSymm : magSym.IsSymm := by
  refine Matrix.IsSymm.ext fun u v => ?_
  fin_cases u <;> fin_cases v <;>
    norm_num [magSym, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Zero-phase agreement on the symmetric edge, entrywise: the
magnetic Laplacian at `Θ = 0` is the complexified classical Laplacian
(the theorem route), and the classical entries are `1`/`-1` raw. -/
theorem magZeroPhase_agreement :
    magneticLaplacian magSym magThetaZero 0 1 = (-(1 : ℝ) : ℂ)
      ∧ magneticLaplacian magSym magThetaZero 0 0 = ((1 : ℝ) : ℂ)
      ∧ (laplacian magSym) 0 1 = -(1 : ℝ)
      ∧ (laplacian magSym) 0 0 = 1 := by
  have hΘ0 : magThetaZero = 0 := by
    ext u v
    fin_cases u <;> fin_cases v <;>
      norm_num [magThetaZero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
  have hdeg0 : deg magSym 0 = 1 := by
    norm_num [deg, magSym, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  have hdm01 : degreeMatrix magSym 0 1 = 0 :=
    degreeMatrix_off_diagonal magSym (by decide : (0 : Fin 2) ≠ 1)
  have hdm00 : degreeMatrix magSym 0 0 = 1 := by
    rw [degreeMatrix_diagonal, hdeg0]
  have he01 : magSym 0 1 = 1 := rfl
  have he00 : magSym 0 0 = 0 := rfl
  have hL01 : (laplacian magSym) 0 1 = -1 := by
    show degreeMatrix magSym 0 1 - magSym 0 1 = -1
    rw [hdm01, he01]
    ring
  have hL00 : (laplacian magSym) 0 0 = 1 := by
    show degreeMatrix magSym 0 0 - magSym 0 0 = 1
    rw [hdm00, he00]
    norm_num
  refine ⟨?_, ?_, hL01, hL00⟩
  · rw [hΘ0, magneticLaplacian_zero_phase_apply_of_isSymm magSym_isSymm]
    exact_mod_cast hL01
  · rw [hΘ0, magneticLaplacian_zero_phase_apply_of_isSymm magSym_isSymm]
    exact_mod_cast hL00

/-- The symmetric-cone single-`W` form at the `π`-flux pair: the cone
theorem transports to `D_sym - W`, and the off-diagonal entry is
`0 - W 0 1 = 0 - (-1) = 1` (since `W 0 1 = 1·e^{iπ} = -1`). -/
theorem magCone_single : magneticLaplacian magSym magThetaPi 0 1 = 1 := by
  rw [magneticLaplacian_eq_single magSym magThetaPi magSym_isSymm
    (by intro u v
        fin_cases u <;> fin_cases v <;>
          norm_num [magThetaPi, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons])]
  show (Matrix.diagonal (fun w => (symDeg magSym w : ℂ)) 0 1
      - magneticMatrix magSym magThetaPi 0 1) = 1
  have hW : magneticMatrix magSym magThetaPi 0 1 = -1 := by
    show (magSym 0 1 : ℂ) * Complex.exp (Complex.I * (magThetaPi 0 1 : ℂ)) = -1
    have h1 : (magSym 0 1 : ℝ) = 1 := rfl
    have h2 : (magThetaPi 0 1 : ℝ) = Real.pi := rfl
    rw [h1, h2, magExp_pi]
    push_cast
    ring
  rw [Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1), hW]
  ring

/-! ### Section B: frustration vs consistency -/

theorem magTri_nonneg : ∀ u v, 0 ≤ magTri u v := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    norm_num [magTri, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]

/-- **The frustrated triangle:** with one `π`-flux edge the gauge
condition forces every potential to vanish — the form is positive
definite. Spectral localization of flux at form level: no eigenvalue
machinery involved, only the gauge characterization. -/
theorem magTri_frustrated (x : Fin 3 → ℂ)
    (h : hermQuadForm (magneticLaplacian magTri magThetaTri) x = 0) : x = 0 := by
  have hg := (magneticQuadForm_eq_zero_iff magTri magThetaTri x magTri_nonneg).1 h
  have htri01 : magTri 0 1 ≠ 0 := by
    norm_num [magTri, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons]
  have htri12 : magTri 1 2 ≠ 0 := by
    norm_num [magTri, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons]
  have htri02 : magTri 0 2 ≠ 0 := by
    norm_num [magTri, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons]
  have ht01 : (magThetaTri 0 1 : ℝ) = Real.pi := rfl
  have ht12 : (magThetaTri 1 2 : ℝ) = 0 := rfl
  have ht02 : (magThetaTri 0 2 : ℝ) = 0 := rfl
  have h01 : x 0 = -(x 1) := by
    have hp := hg 0 1 htri01
    simp only [ht01] at hp
    rw [magExp_pi] at hp
    simpa using hp
  have h12 : x 1 = x 2 := by
    have hp := hg 1 2 htri12
    simp only [ht12] at hp
    simpa using hp
  have h02 : x 0 = x 2 := by
    have hp := hg 0 2 htri02
    simp only [ht02] at hp
    simpa using hp
  have e1 : -(x 1) = -(x 2) := by rw [h12]
  have ex : x 0 = -(x 0) := by
    have hx02 : x 2 = x 0 := h02.symm
    calc x 0 = -(x 1) := h01
      _ = -(x 2) := e1
      _ = -(x 0) := by rw [← hx02]
  have h2 : x 0 + x 0 = 0 := by
    nth_rewrite 1 [ex]
    ring
  have hx0 : x 0 = 0 := by
    rcases mul_eq_zero.1 (show 2 * x 0 = 0 by rw [two_mul]; exact h2) with hz | hxz
    · exact absurd hz (by norm_num)
    · exact hxz
  funext i
  fin_cases i
  · exact hx0
  · show x 1 = 0
    rw [show x 1 = x 0 from h12.trans h02.symm]; exact hx0
  · show x 2 = 0
    rw [show x 2 = x 0 from h02.symm]; exact hx0

/-- The positive-definite form consequence: every nonzero vector has
strictly positive magnetic energy on the frustrated triangle. -/
theorem magTri_frustrated_posdef (x : Fin 3 → ℂ) (hx : x ≠ 0) :
    0 < (hermQuadForm (magneticLaplacian magTri magThetaTri) x).re := by
  have h0 : hermQuadForm (magneticLaplacian magTri magThetaTri) x ≠ 0 :=
    fun h => hx (magTri_frustrated x h)
  rw [magnetic_energy_real] at h0 ⊢
  rw [Complex.ofReal_re]
  have hnn : ∀ u : Fin 3, u ∈ Finset.univ → 0 ≤ ∑ v,
      magTri u v * Complex.normSq (x u - Complex.exp (Complex.I * magThetaTri u v) * x v) / 2 := by
    intro u _
    refine Finset.sum_nonneg ?_
    intro v _
    exact div_nonneg (mul_nonneg (magTri_nonneg u v) (Complex.normSq_nonneg _))
      (by norm_num)
  rcases lt_or_eq_of_le (Finset.sum_nonneg hnn) with h | h
  · exact h
  · exact absurd h (fun h0' => h0 (by rw [← h0']; push_cast; rfl))

/-- **The consistent flux:** the same `π` flux on a single edge is not
frustration — the antipodal phase potential `![1, -1]` lies in the
kernel, through the gauge iff's reverse direction. -/
theorem magK2_antipodal_kernel :
    hermQuadForm (magneticLaplacian magSym magThetaPi) ![1, -1] = 0 := by
  refine (magneticQuadForm_eq_zero_iff magSym magThetaPi ![1, -1]
    (by intro u v
        fin_cases u <;> fin_cases v <;>
          norm_num [magSym, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons])).2 ?_
  intro u v huv
  match u, v with
  | ⟨0, _⟩, ⟨1, _⟩ =>
    show ![1, -1] 0 = Complex.exp (Complex.I * ↑(magThetaPi 0 1)) * ![1, -1] 1
    rw [show ((magThetaPi 0 1 : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) from rfl, magExp_pi]
    norm_num [Matrix.cons_val_zero, Matrix.head_cons]
  | ⟨1, _⟩, ⟨0, _⟩ =>
    show ![1, -1] 1 = Complex.exp (Complex.I * ↑(magThetaPi 1 0)) * ![1, -1] 0
    rw [show ((magThetaPi 1 0 : ℝ) : ℂ) = ((-Real.pi : ℝ) : ℂ) from rfl, magExp_neg_pi]
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
  | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl huv
  | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl huv

/-- The antipodal kernel cross-checked through the raw energy: every
edge energy vanishes because `e^{iπ}·(-1) = 1` exactly cancels. -/
theorem magK2_antipodal_energy : ∑ u, ∑ v,
    (magSym u v : ℂ) * Complex.normSq
      (![1, -1] u - Complex.exp (Complex.I * magThetaPi u v) * ![1, -1] v) / 2 = 0 := by
  have h00 : (magSym 0 0 : ℝ) = 0 := rfl
  have h01 : (magSym 0 1 : ℝ) = 1 := rfl
  have h10 : (magSym 1 0 : ℝ) = 1 := rfl
  have h11 : (magSym 1 1 : ℝ) = 0 := rfl
  have ht00 : (magThetaPi 0 0 : ℝ) = 0 := rfl
  have ht01 : (magThetaPi 0 1 : ℝ) = Real.pi := rfl
  have ht10 : (magThetaPi 1 0 : ℝ) = -Real.pi := rfl
  have ht11 : (magThetaPi 1 1 : ℝ) = 0 := rfl
  norm_num [h00, h01, h10, h11, ht00, ht01, ht10, ht11,
    magExp_pi, magExp_neg_pi_pushed, Complex.exp_zero]

/-! ### Section C: the classical bridge at zero phase -/

/-- At zero phase the constant complex vector lies in the kernel — the
complexified classical kernel through the gauge iff. -/
theorem magZero_kernel :
    hermQuadForm (magneticLaplacian magSym magThetaZero) (fun _ => (1 : ℂ)) = 0 := by
  refine (magneticQuadForm_eq_zero_iff magSym magThetaZero (fun _ => (1 : ℂ))
    (by intro u v
        fin_cases u <;> fin_cases v <;>
          norm_num [magSym, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons])).2 ?_
  intro u v huv
  match u, v with
  | ⟨0, _⟩, ⟨1, _⟩ =>
    show (1 : ℂ) = Complex.exp (Complex.I * ↑(magThetaZero 0 1)) * 1
    norm_num [magThetaZero, Complex.exp_zero]
  | ⟨1, _⟩, ⟨0, _⟩ =>
    show (1 : ℂ) = Complex.exp (Complex.I * ↑(magThetaZero 1 0)) * 1
    norm_num [magThetaZero, Complex.exp_zero]
  | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl huv
  | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl huv

/-- The antipodal vector is provably *outside* the zero-phase kernel
(the energy is `½[|1-(-1)|² + |-1-1|²] = 4`): the `π` flux is exactly
what moved the kernel from the constants to the antipodal phases —
sections B and C joined. -/
theorem magZero_antipodal_outside :
    hermQuadForm (magneticLaplacian magSym magThetaZero) ![1, -1] = 4 := by
  rw [magnetic_energy]
  norm_num [magSym, magThetaZero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Complex.normSq_apply]

/-! ### Section D: the nonnegativity fence -/

/-- PSD refuted on symmetric *signed* input: at the indicator test
vector the magnetic quadratic form's real part is exactly `-1`
(`½[-1·|1-0|² + -1·|0-1|²] = -1`). The hypothesis-free conclusion is
false; `hA : 0 ≤ A` is the fence — the signed-graph surface. -/
theorem magSigned_PSD_refuted :
    (hermQuadForm (magneticLaplacian magSigned magThetaZero) ![1, 0]).re = -1
      ∧ ¬ 0 ≤ (hermQuadForm (magneticLaplacian magSigned magThetaZero) ![1, 0]).re := by
  have h01 : (magSigned 0 1 : ℝ) = -1 := rfl
  have h10 : (magSigned 1 0 : ℝ) = -1 := rfl
  rw [magnetic_energy_real, Complex.ofReal_re]
  constructor
  · norm_num [h01, h10, magThetaZero, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  · norm_num [h01, h10, magThetaZero, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

/-! ### Section E: the structural pins

The six structural theorems the consumption census found inert
(`conj_exp_I_mul_exp_I`, `hermQuadForm_eq_zero_of_mulVec_eq_zero`,
`magneticLaplacian_mulVec_eq_zero_iff`,
`magneticLaplacian_mulVec_eq_zero_of_forall_exp_mul_eq`,
`magneticQuadForm_im_eq_zero`, `magneticQuadForm_re_nonneg`),
consumed for the first time at the delivered fixtures — the pins
method's fourth application and its first complex-valued target.
-/

/-- Weight nonnegativity of the asymmetric fixture (the PSD/kernel-iff
hypothesis, dischargeable on genuinely directed input). -/
theorem magA_nonneg : ∀ u v, 0 ≤ magA u v := by
  intro u v
  fin_cases u <;> fin_cases v <;>
    norm_num [magA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **Pin: the unit-phase pairing at `π`** — `conj (e^{iπ}) · e^{iπ} = 1`
by the theorem, the pairing the K₂ alignment discharges lean on. -/
theorem magPairing_pi_pin :
    conj (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)))
      * Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = 1 :=
  conj_exp_I_mul_exp_I Real.pi

set_option linter.unnecessarySimpa false in
/-- **Pin: the unit-phase pairing at a genuinely complex phase** — the
numeric identity `conj (I) · I = 1` derived THROUGH the theorem at
`π/2` (not by direct `I·I` arithmetic). -/
theorem magPairing_I_pin : conj (Complex.I) * Complex.I = 1 := by
  have h := conj_exp_I_mul_exp_I (Real.pi / 2)
  rw [magExp_half_pi_raw, Complex.conj_I] at h
  simpa [Complex.I_mul_I] using h

/-- **Pin: real-valuedness promoted** — at the genuinely complex test
vector `![1, I]` the form's imaginary part vanishes by the theorem, and
the full complex value `2` is ASSEMBLED from the raw real energy plus
that vanishing imaginary part (the promotion is load-bearing: `.re = 2`
alone does not give `= 2`). -/
theorem magIm_pin :
    (hermQuadForm (magneticLaplacian magA magTheta) ![1, Complex.I]).im = 0
      ∧ hermQuadForm (magneticLaplacian magA magTheta) ![1, Complex.I] = 2 := by
  have him : (hermQuadForm (magneticLaplacian magA magTheta) ![1, Complex.I]).im = 0 :=
    magneticQuadForm_im_eq_zero magA magTheta _
  have hre : (hermQuadForm (magneticLaplacian magA magTheta) ![1, Complex.I]).re = 2 := by
    rw [magnetic_energy_real, Complex.ofReal_re]
    norm_num [magA, magTheta, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, magExp_pi, magExp_half_pi, Complex.normSq_apply]
  refine ⟨him, ?_⟩
  exact Complex.ext_iff.2 ⟨hre, by rw [him]; norm_num⟩

/-- **Pin: PSD at asymmetric input** — the theorem applies with the
weights hypothesis discharged on genuinely directed input (`0/2/1/0`),
and the bound is nonvacuous: the pinned energy at this fixture and
vector is `5` (`magEnergy_pin`). -/
theorem magPSD_pin :
    0 ≤ (hermQuadForm (magneticLaplacian magA magTheta) ![1, 1]).re
      ∧ (hermQuadForm (magneticLaplacian magA magTheta) ![1, 1]).re = 5 := by
  refine ⟨magneticQuadForm_re_nonneg magA magTheta _ magA_nonneg, ?_⟩
  rw [magnetic_energy_real, Complex.ofReal_re]
  norm_num [magA, magTheta, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, magExp_pi, magExp_half_pi, Complex.normSq_apply]

/-- **Pin: the row-algebra reverse direction at the `π`-flux edge** —
the antipodal potential is KILLED by the magnetic Laplacian, through
the hypothesis-free-on-weights row algebra. -/
theorem magK2_mulVec_zero :
    magneticLaplacian magSym magThetaPi *ᵥ ![1, -1] = 0 := by
  refine magneticLaplacian_mulVec_eq_zero_of_forall_exp_mul_eq magSym magThetaPi ![1, -1] ?_
  intro u v huv
  match u, v with
  | ⟨0, _⟩, ⟨1, _⟩ =>
    show ![1, -1] 0 = Complex.exp (Complex.I * ↑(magThetaPi 0 1)) * ![1, -1] 1
    rw [show ((magThetaPi 0 1 : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) from rfl, magExp_pi]
    norm_num [Matrix.cons_val_zero, Matrix.head_cons]
  | ⟨1, _⟩, ⟨0, _⟩ =>
    show ![1, -1] 1 = Complex.exp (Complex.I * ↑(magThetaPi 1 0)) * ![1, -1] 0
    rw [show ((magThetaPi 1 0 : ℝ) : ℂ) = ((-Real.pi : ℝ) : ℂ) from rfl, magExp_neg_pi]
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
  | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl huv
  | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl huv

/-- **Pin: form-level kernel membership through the ACTION route** —
`magK2_antipodal_kernel`'s pinned conclusion, re-derived via
`M *ᵥ x = 0` (the row algebra) plus the kernel-to-form helper. -/
theorem magK2_action_form_zero :
    hermQuadForm (magneticLaplacian magSym magThetaPi) ![1, -1] = 0 :=
  hermQuadForm_eq_zero_of_mulVec_eq_zero _ _ magK2_mulVec_zero

/-- **Pin: the kernel iff's reverse direction at zero phase** — the
constant potential is killed, through the iff applied backwards (the
alignment at `e^{i·0} = 1`). -/
theorem magZero_mulVec_kernel :
    magneticLaplacian magSym magThetaZero *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  refine (magneticLaplacian_mulVec_eq_zero_iff magSym magThetaZero
    (by intro u v
        fin_cases u <;> fin_cases v <;>
          norm_num [magSym, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons]) _).2 ?_
  intro u v huv
  match u, v with
  | ⟨0, _⟩, ⟨1, _⟩ =>
    show (1 : ℂ) = Complex.exp (Complex.I * ↑(magThetaZero 0 1)) * 1
    norm_num [magThetaZero, Complex.exp_zero]
  | ⟨1, _⟩, ⟨0, _⟩ =>
    show (1 : ℂ) = Complex.exp (Complex.I * ↑(magThetaZero 1 0)) * 1
    norm_num [magThetaZero, Complex.exp_zero]
  | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl huv
  | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl huv

/-- **Pin: the classical join, independently** — the same zero-phase
action-kernel fact through the CONE AGREEMENT route: entrywise the
magnetic operator is the complexified classical Laplacian, whose
constant-kernel property is raw arithmetic (`1 - 1 = 0` per row). Two
independent engines for one pinned fact; each fails if its own layer is
wrong. -/
theorem magZero_mulVec_kernel_classical :
    magneticLaplacian magSym magThetaZero *ᵥ (fun _ => (1 : ℂ)) = 0 := by
  have hΘ0 : magThetaZero = 0 := by
    ext u v
    fin_cases u <;> fin_cases v <;>
      norm_num [magThetaZero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
  have hdeg : ∀ i : Fin 2, deg magSym i = 1 := by
    intro i
    fin_cases i <;>
      norm_num [deg, magSym, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
  have hLdiag : ∀ i : Fin 2, (laplacian magSym) i i = 1 := by
    intro i
    show degreeMatrix magSym i i - magSym i i = 1
    rw [degreeMatrix_diagonal, hdeg i]
    fin_cases i <;>
      norm_num [magSym, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hLoff : ∀ i j : Fin 2, i ≠ j → (laplacian magSym) i j = -1 := by
    intro i j hij
    show degreeMatrix magSym i j - magSym i j = -1
    rw [degreeMatrix_off_diagonal magSym hij]
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | norm_num [magSym, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  funext i
  rw [Matrix.mulVec, Matrix.dotProduct, hΘ0, Fin.sum_univ_two, Pi.zero_apply]
  have h0 : magneticLaplacian magSym (0 : Matrix (Fin 2) (Fin 2) ℝ) i 0
      = ((laplacian magSym) i 0 : ℂ) :=
    magneticLaplacian_zero_phase_apply_of_isSymm magSym_isSymm i 0
  have h1 : magneticLaplacian magSym (0 : Matrix (Fin 2) (Fin 2) ℝ) i 1
      = ((laplacian magSym) i 1 : ℂ) :=
    magneticLaplacian_zero_phase_apply_of_isSymm magSym_isSymm i 1
  rw [h0, h1]
  fin_cases i
  · show ((laplacian magSym) 0 0 : ℂ) * 1 + ((laplacian magSym) 0 1 : ℂ) * 1 = 0
    rw [hLdiag 0, hLoff 0 1 (by decide)]
    norm_num
  · show ((laplacian magSym) 1 0 : ℂ) * 1 + ((laplacian magSym) 1 1 : ℂ) * 1 = 0
    rw [hLdiag 1, hLoff 1 0 (by decide)]
    norm_num

/-- **Pin: the kernel iff's forward direction at the frustrated
triangle** — action-level kernel membership forces the potential to
vanish (the alignment the iff supplies, replayed). -/
theorem magTri_kernel_frustrated (x : Fin 3 → ℂ)
    (h : magneticLaplacian magTri magThetaTri *ᵥ x = 0) : x = 0 := by
  have hg := (magneticLaplacian_mulVec_eq_zero_iff magTri magThetaTri magTri_nonneg x).1 h
  have htri01 : magTri 0 1 ≠ 0 := by
    norm_num [magTri, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons]
  have htri12 : magTri 1 2 ≠ 0 := by
    norm_num [magTri, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons]
  have htri02 : magTri 0 2 ≠ 0 := by
    norm_num [magTri, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons]
  have ht01 : (magThetaTri 0 1 : ℝ) = Real.pi := rfl
  have ht12 : (magThetaTri 1 2 : ℝ) = 0 := rfl
  have ht02 : (magThetaTri 0 2 : ℝ) = 0 := rfl
  have h01 : x 0 = -(x 1) := by
    have hp := hg 0 1 htri01
    simp only [ht01] at hp
    rw [magExp_pi] at hp
    simpa using hp
  have h12 : x 1 = x 2 := by
    have hp := hg 1 2 htri12
    simp only [ht12] at hp
    simpa using hp
  have h02 : x 0 = x 2 := by
    have hp := hg 0 2 htri02
    simp only [ht02] at hp
    simpa using hp
  have e1 : -(x 1) = -(x 2) := by rw [h12]
  have ex : x 0 = -(x 0) := by
    have hx02 : x 2 = x 0 := h02.symm
    calc x 0 = -(x 1) := h01
      _ = -(x 2) := e1
      _ = -(x 0) := by rw [← hx02]
  have h2 : x 0 + x 0 = 0 := by
    nth_rewrite 1 [ex]
    ring
  have hx0 : x 0 = 0 := by
    rcases mul_eq_zero.1 (show 2 * x 0 = 0 by rw [two_mul]; exact h2) with hz | hxz
    · exact absurd hz (by norm_num)
    · exact hxz
  funext i
  fin_cases i
  · exact hx0
  · show x 1 = 0
    rw [show x 1 = x 0 from h12.trans h02.symm]; exact hx0
  · show x 2 = 0
    rw [show x 2 = x 0 from h02.symm]; exact hx0

/-- **Pin: the negative action-level witness at the frustrated
triangle** — the constant potential is NOT killed, THROUGH the iff's
forward direction (were the kernel larger than the aligned potentials,
this would fail). -/
theorem magTri_const_action_ne_zero :
    ¬ (magneticLaplacian magTri magThetaTri *ᵥ ![1, 1, 1] = 0) := by
  intro h
  have hg := (magneticLaplacian_mulVec_eq_zero_iff magTri magThetaTri magTri_nonneg _).1 h
  have htri01 : magTri 0 1 ≠ 0 := by
    norm_num [magTri, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons]
  have hp := hg 0 1 htri01
  simp only [show (magThetaTri 0 1 : ℝ) = Real.pi from rfl] at hp
  rw [magExp_pi] at hp
  norm_num [Matrix.cons_val_zero, Matrix.head_cons] at hp

/-- **Pin: directed frustration** — the asymmetric fixture's phase pair
(`π` on `0→1`, `π/2` on `1→0`) is frustrated: the kernel
characterization forces every killed potential to vanish, on GENUINELY
DIRECTED input with genuinely complex phases (`x₀ = -x₁` and
`x₁ = I·x₀` give `(1 + I)·x₀ = 0`). -/
theorem magAsym_kernel_trivial (x : Fin 2 → ℂ)
    (h : magneticLaplacian magA magTheta *ᵥ x = 0) : x = 0 := by
  have hg := (magneticLaplacian_mulVec_eq_zero_iff magA magTheta magA_nonneg x).1 h
  have hA01 : magA 0 1 ≠ 0 := by
    norm_num [magA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hA10 : magA 1 0 ≠ 0 := by
    norm_num [magA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hp01 := hg 0 1 hA01
  have hp10 := hg 1 0 hA10
  rw [show (magTheta 0 1 : ℝ) = Real.pi from rfl, magExp_pi] at hp01
  rw [show (magTheta 1 0 : ℝ) = Real.pi / 2 from rfl, magExp_half_pi_raw] at hp10
  have h01 : x 0 = -(x 1) := by simpa using hp01
  have h10 : x 1 = Complex.I * x 0 := by simpa using hp10
  have key : x 0 + Complex.I * x 0 = 0 := by
    calc x 0 + Complex.I * x 0 = -(x 1) + Complex.I * x 0 := by rw [h01]
      _ = -(Complex.I * x 0) + Complex.I * x 0 := by rw [← h10]
      _ = 0 := by ring
  have hne : (1 : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have hre := (Complex.ext_iff.1 hz).1
    norm_num at hre
  have hx0 : x 0 = 0 := by
    have hmul : ((1 : ℂ) + Complex.I) * x 0 = 0 := by
      rw [add_mul, one_mul]
      exact key
    rcases mul_eq_zero.1 hmul with h1 | h2
    · exact absurd h1 hne
    · exact h2
  funext i
  fin_cases i
  · exact hx0
  · show x 1 = 0
    rw [h10, hx0]
    ring

end SpectralGraphTheory.QA
