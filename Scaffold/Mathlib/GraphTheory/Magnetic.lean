/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Scaffold.Mathlib.GraphTheory.Directed
import Scaffold.Mathlib.GraphTheory.Spectral

/-!
# The magnetic Laplacian

The first slice of the magnetic-Laplacian program (backlog item 8's
reserved directed-axis slice, `proposals/magnetic-laplacian.md`,
delivered 2026-08-25): the directed-native **magnetic Laplacian** — the
shelf's first complex-valued object — with the layer every consumer
needs and nothing beyond it.

The operator, at the Hermitian-part convention of Crucini–Pérez–Bungert–
Van Mieghem (*The magnetic Laplacian of directed graphs*, Linear Algebra
Appl. 2023; arXiv:2202.02497 §2 — route provenance; the statements here
are proved, not admitted):

`M(A, Θ) := D_sym − ½(W + Wᴴ)`,  `W := A ∘ e^{iΘ}` entrywise,
`D_sym := ½(outDeg + inDeg)` — with real (possibly asymmetric) weights
`A` and an arbitrary real phase matrix `Θ`.

Everything here is proved; no axiom is admitted. Two structural facts
carry the design:

* **Hermitian by construction, hypothesis-free** (`magneticLaplacian_
  isHermitian`): the Hermitian part `½(W + Wᴴ)` makes symmetry
  structural — the same convention decision as `directedNormalizedLaplacian`
  (delivered 2026-08-22), putting directed input at the center rather
  than the periphery. The classical single-`W` form is *derived* on the
  symmetric/antisymmetric cone (`magneticLaplacian_eq_single`).

* **The magnetic energy identity, hypothesis-free**
  (`magnetic_energy`): `x*Mx = ½ ∑ A_uv |x_u − e^{iΘ_uv} x_v|²` — the
  finite-algebra Dirichlet principle. It yields PSD on nonnegative
  weights (`magneticQuadForm_re_nonneg`) and the **gauge
  characterization** of the kernel (`magneticQuadForm_eq_zero_iff`):
  `x*Mx = 0 ↔ x_u = e^{iΘ_uv} x_v` on every positive edge — the
  balanced-potential condition. A frustrated cycle forces the kernel
  trivial (form-level positive definiteness — *spectral localization of
  flux* with no complex spectral theorem anywhere).

* **The kernel at the action level**
  (`magneticLaplacian_mulVec_eq_zero_iff`, added 2026-08-26 with the
  signed-graph program, `proposals/signed-graphs-balance.md`): the
  gauge characterization promoted from form level to the kernel — on
  nonnegative weights, `M *ᵥ x = 0 ↔ x_u = e^{iΘ_uv} x_v` on every
  positive edge, the missing half being pure row algebra at unit
  modulus. This is the statement shape the signed-graph balance
  theorem consumes at the π-flux.

At zero phase the operator is the complexified classical Laplacian of
the symmetrized weights (`magneticLaplacian_zero_phase_apply`) — on
symmetric `A`, of `laplacian A` itself: the join with the real shelf.

## Scope

No eigenvalues of `M`, no magnetic Cheeger or synchronization bounds —
the pin *has* Hermitian spectral theory
(`Mathlib/LinearAlgebra/Matrix/Spectrum.lean`), so those are priced
follow-ons in the proposal, not obstructions.
-/

open scoped BigOperators Matrix ComplexConjugate

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Definitions
-/

/-- The symmetrized degree: half the in-plus-out degree sum — the
fan-in/fan-out degree split the magnetic energy identity's diagonal
demands. -/
noncomputable def symDeg (A : Matrix V V ℝ) (u : V) : ℝ :=
  (outDeg A u + inDeg A u) / 2

/-- The entrywise phase-weighted complex adjacency
`W := A ∘ e^{iΘ}` — `(A ∘ e^{iΘ}) u v = A u v * e^{i Θ u v}`. Defined
for ANY real weight matrix (asymmetric included) and ANY real phase
matrix; no symmetry or antisymmetry hypothesis is carried by the
definition. -/
noncomputable def magneticMatrix (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) :
    Matrix V V ℂ :=
  fun u v => A u v * Complex.exp (Complex.I * Θ u v)

/-- The **magnetic Laplacian** at the Hermitian-part convention:
`M := D_sym − ½(W + Wᴴ)` with `W := magneticMatrix A Θ` — Hermitian by
construction for any real `A` and any real `Θ` (see
`magneticLaplacian_isHermitian`), directed-native (the single-`W`
classical form is derived on the symmetric/antisymmetric cone by
`magneticLaplacian_eq_single`). -/
noncomputable def magneticLaplacian (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) :
    Matrix V V ℂ :=
  Matrix.diagonal (fun u => (symDeg A u : ℂ))
    - (1 / 2 : ℂ) • (magneticMatrix A Θ + (magneticMatrix A Θ)ᴴ)

/-- The sesquilinear quadratic form `hermQuadForm M x = ∑ i, conj (x i) *
(M *ᵥ x) i` — the complex analogue of the shelf's `quadForm` (Mathlib's
`Matrix.dotProduct` is bilinear, so the complex form needs its own
carrier). Real-valued on Hermitian input; see
`magneticQuadForm_im_eq_zero`. -/
noncomputable def hermQuadForm (M : Matrix V V ℂ) (x : V → ℂ) : ℂ :=
  ∑ i, conj (x i) * (M *ᵥ x) i

/-!
## The Hermitian structure (hypothesis-free)
-/

omit [DecidableEq V] in
omit [Fintype V] [DecidableEq V] in
/-- The phase-weighted adjacency is Hermitian on the symmetric/
antisymmetric cone: `A` symmetric and `Θ` entrywise antisymmetric make
`Wᴴ = W`, since `conj (A u v * e^{iΘ u v}) = A u v * e^{iΘ u v}`. -/
theorem magneticMatrix_isHermitian (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    (hA : A.IsSymm) (hΘ : ∀ u v, Θ u v = -Θ v u) :
    (magneticMatrix A Θ).IsHermitian := by
  have hconjt : ∀ t : ℝ,
      conj (Complex.exp (Complex.I * (t : ℂ)))
        = Complex.exp (Complex.I * (-(t : ℝ) : ℂ)) := by
    intro t
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [Matrix.IsHermitian.ext_iff]
  intro u v
  simp only [Matrix.conjTranspose_apply, magneticMatrix, Complex.star_def, map_mul,
    Complex.conj_ofReal, hA.apply]
  rw [hconjt (Θ v u), hΘ v u, Complex.ofReal_neg, neg_neg]

/-- The magnetic Laplacian is Hermitian **for any real weights and any
phases** — hypothesis-free: the diagonal is real and the off-diagonal
defining halves are conjugates of each other. The Hermitian-part
convention makes the symmetry structural. -/
theorem magneticLaplacian_isHermitian (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) :
    (magneticLaplacian A Θ).IsHermitian := by
  rw [Matrix.IsHermitian, magneticLaplacian, Matrix.conjTranspose_sub,
    Matrix.diagonal_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  have hc : (star (1 / 2 : ℂ)) = 1 / 2 := by
    norm_num [Complex.star_def, map_div₀, Complex.conj_ofNat]
  have hd : (star fun u => (symDeg A u : ℂ)) = fun u => (symDeg A u : ℂ) := by
    funext u; simp [Complex.star_def, Complex.conj_ofReal]
  have ha : (1 / 2 : ℂ) • ((magneticMatrix A Θ)ᴴ + magneticMatrix A Θ)
      = (1 / 2 : ℂ) • (magneticMatrix A Θ + (magneticMatrix A Θ)ᴴ) := by
    rw [add_comm]
  rw [hc, hd, ha]

/-!
## The energy identity (hypothesis-free)
-/

/-- Entry action of the magnetic Laplacian: the symmetrized degree on
the flow side, half the conjugate-paired phase couplings on the other.
Useful interface lemma; also the engine behind `magnetic_energy`. -/
theorem magneticLaplacian_mulVec_apply (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    (x : V → ℂ) (i : V) :
    (magneticLaplacian A Θ *ᵥ x) i
      = (symDeg A i : ℂ) * x i
        - (1 / 2 : ℂ) * (∑ j, magneticMatrix A Θ i j * x j
          + ∑ j, conj (magneticMatrix A Θ j i) * x j) := by
  show ((Matrix.diagonal (fun u => (symDeg A u : ℂ))
      - (1 / 2 : ℂ) • (magneticMatrix A Θ + (magneticMatrix A Θ)ᴴ)) *ᵥ x) i = _
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.add_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.mulVec_diagonal, Matrix.mulVec,
    Matrix.dotProduct, Matrix.mulVec, Matrix.dotProduct]
  simp only [Matrix.conjTranspose_apply, Complex.star_def]

omit [DecidableEq V] in
/-- Scalar expansion of one magnetic edge energy: with a unit-modulus
phase `e`, `|z − e·w|² = |z|² + |w|² − (conj z · e · w + conj e · conj w · z)`
— the two cross terms are conjugates of each other. -/
private theorem normSq_sub_exp (z w : ℂ) (t : ℝ) :
    ((Complex.normSq (z - Complex.exp (Complex.I * t) * w) : ℂ))
      = conj z * z + conj w * w
        - (conj z * Complex.exp (Complex.I * t) * w
          + conj (Complex.exp (Complex.I * t)) * conj w * z) := by
  have he : conj (Complex.exp (Complex.I * (t : ℂ)))
      * Complex.exp (Complex.I * (t : ℂ)) = 1 := by
    have h0 : conj (Complex.I * (t : ℂ)) + Complex.I * (t : ℂ) = 0 := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [← Complex.exp_conj, ← Complex.exp_add, h0, Complex.exp_zero]
  have h4 : conj (Complex.exp (Complex.I * (t:ℂ))) * conj w
      * (Complex.exp (Complex.I * (t:ℂ)) * w) = conj w * w := by
    have h5 : conj (Complex.exp (Complex.I * (t:ℂ))) * conj w
        * (Complex.exp (Complex.I * (t:ℂ)) * w)
        = (conj (Complex.exp (Complex.I * (t:ℂ)))
            * Complex.exp (Complex.I * (t:ℂ))) * (conj w * w) := by ring
    rw [h5, he, one_mul]
  rw [Complex.normSq_eq_conj_mul_self, map_sub, map_mul, sub_mul, mul_sub, mul_sub, h4]
  ring

private theorem hermQuadForm_expansion (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    (x : V → ℂ) :
    hermQuadForm (magneticLaplacian A Θ) x
      = ∑ i, (symDeg A i : ℂ) * (conj (x i) * x i)
        - (1 / 2 : ℂ) * ∑ i, ∑ j, conj (x i) * magneticMatrix A Θ i j * x j
        - (1 / 2 : ℂ) * ∑ i, ∑ j, conj (x i) * conj (magneticMatrix A Θ j i) * x j := by
  simp only [hermQuadForm, magneticLaplacian_mulVec_apply]
  have key : ∀ i : V,
      conj (x i) * ((symDeg A i : ℂ) * x i
        - (1 / 2 : ℂ) * ((∑ j, magneticMatrix A Θ i j * x j)
          + ∑ j, conj (magneticMatrix A Θ j i) * x j))
      = (symDeg A i : ℂ) * (conj (x i) * x i)
        - (1 / 2 : ℂ) * ∑ j, conj (x i) * (magneticMatrix A Θ i j * x j)
        - (1 / 2 : ℂ) * ∑ j, conj (x i) * (conj (magneticMatrix A Θ j i) * x j) := by
    intro i
    have hring : conj (x i) * ((symDeg A i : ℂ) * x i
        - (1 / 2 : ℂ) * ((∑ j, magneticMatrix A Θ i j * x j)
          + ∑ j, conj (magneticMatrix A Θ j i) * x j))
      = (symDeg A i : ℂ) * (conj (x i) * x i)
        - (1 / 2 : ℂ) * (conj (x i) * ∑ j, magneticMatrix A Θ i j * x j)
        - (1 / 2 : ℂ) * (conj (x i) * ∑ j, conj (magneticMatrix A Θ j i) * x j) := by
      ring
    have f1 : conj (x i) * ∑ j, magneticMatrix A Θ i j * x j
        = ∑ j, conj (x i) * magneticMatrix A Θ i j * x j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have f2 : conj (x i) * ∑ j, conj (magneticMatrix A Θ j i) * x j
        = ∑ j, conj (x i) * conj (magneticMatrix A Θ j i) * x j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hring, f1, f2]
    have e1 : ∀ j : V, conj (x i) * (magneticMatrix A Θ i j * x j)
        = conj (x i) * magneticMatrix A Θ i j * x j := fun j => by ring
    have e2 : ∀ j : V, conj (x i) * (conj (magneticMatrix A Θ j i) * x j)
        = conj (x i) * conj (magneticMatrix A Θ j i) * x j := fun j => by ring
    simp only [e1, e2]
  simp only [key]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have g1 : ∀ i : V, ∑ j, conj (x i) * (magneticMatrix A Θ i j * x j)
      = ∑ j, conj (x i) * magneticMatrix A Θ i j * x j :=
    fun i => Finset.sum_congr rfl fun j _ => by ring
  have g2 : ∀ i : V, ∑ j, conj (x i) * (conj (magneticMatrix A Θ j i) * x j)
      = ∑ j, conj (x i) * conj (magneticMatrix A Θ j i) * x j :=
    fun i => Finset.sum_congr rfl fun j _ => by ring
  simp only [g1, g2]

/-- **The magnetic energy identity** — hypothesis-free: for ANY real
weights (asymmetric included) and ANY phases,
`x*Mx = ½ ∑ A_uv |x_u − e^{iΘ_uv} x_v|²`. The finite-algebra Dirichlet
principle of the magnetic program: the quadratic form measures phase
frustration along edges. Everything downstream (PSD, the gauge
characterization) reads off this identity. -/
theorem magnetic_energy (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) (x : V → ℂ) :
    hermQuadForm (magneticLaplacian A Θ) x
      = ∑ u, ∑ v,
          (A u v : ℂ) * Complex.normSq (x u - Complex.exp (Complex.I * Θ u v) * x v) / 2 := by
  classical
  rw [hermQuadForm_expansion A Θ x]
  -- per-entry expansion of the energy summand
  have step1 : ∀ u v : V,
      ((A u v : ℂ) * Complex.normSq (x u - Complex.exp (Complex.I * Θ u v) * x v) / 2)
        = (A u v : ℂ) * (conj (x u) * x u) / 2 + (A u v : ℂ) * (conj (x v) * x v) / 2
          - (1 / 2 : ℂ) * (conj (x u) * magneticMatrix A Θ u v * x v)
          - (1 / 2 : ℂ)
            * ((A u v : ℂ) * conj (Complex.exp (Complex.I * (Θ u v : ℂ)))
              * (conj (x v) * x u)) := by
    intro u v
    have hW : magneticMatrix A Θ u v
        = (A u v : ℂ) * Complex.exp (Complex.I * (Θ u v : ℂ)) := rfl
    rw [normSq_sub_exp, hW]
    ring
  -- the diagonal sum splits into the out- and in-degree halves
  have hdiag : ∑ i, (symDeg A i : ℂ) * (conj (x i) * x i)
      = ∑ u, ∑ v, (A u v : ℂ) * (conj (x u) * x u) / 2
        + ∑ u, ∑ v, (A u v : ℂ) * (conj (x v) * x v) / 2 := by
    have hout : ∑ u, ∑ v, (A u v : ℂ) * (conj (x u) * x u) / 2
        = ∑ u, ((outDeg A u / 2 : ℝ) : ℂ) * (conj (x u) * x u) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_div, ← Finset.sum_mul]
      have hsum : (∑ v, (A u v : ℂ)) = ((outDeg A u : ℝ) : ℂ) := by
        simp [outDeg, ← Complex.ofReal_sum]
      rw [hsum]
      push_cast
      ring
    have hin : ∑ u, ∑ v, (A u v : ℂ) * (conj (x v) * x v) / 2
        = ∑ u, ((inDeg A u / 2 : ℝ) : ℂ) * (conj (x u) * x u) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_div, ← Finset.sum_mul]
      have hsum : (∑ v, (A v u : ℂ)) = ((inDeg A u : ℝ) : ℂ) := by
        simp [inDeg, ← Complex.ofReal_sum]
      rw [hsum]
      push_cast
      ring
    rw [hout, hin, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show symDeg A i = (outDeg A i + inDeg A i) / 2 from rfl]
    push_cast
    field_simp
    ring
  -- the first cross sum matches term by term
  have hc1 : (1 / 2 : ℂ) * ∑ i, ∑ j, conj (x i) * magneticMatrix A Θ i j * x j
      = ∑ u, ∑ v, (1 / 2 : ℂ) * (conj (x u) * magneticMatrix A Θ u v * x v) := by
    simp only [Finset.mul_sum]
  -- the second cross sum: index swap plus the conjugate-entry form
  have hc2s : ∑ i, ∑ j, conj (x i) * conj (magneticMatrix A Θ j i) * x j
      = ∑ u, ∑ v, (A u v : ℂ) * conj (Complex.exp (Complex.I * (Θ u v : ℂ)))
          * (conj (x v) * x u) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hWc : conj (magneticMatrix A Θ u v)
        = (A u v : ℂ) * conj (Complex.exp (Complex.I * (Θ u v : ℂ))) := by
      rw [show magneticMatrix A Θ u v
          = (A u v : ℂ) * Complex.exp (Complex.I * (Θ u v : ℂ)) from rfl,
        map_mul, Complex.conj_ofReal]
    rw [hWc]
    ring
  have hc2 : (1 / 2 : ℂ) * ∑ i, ∑ j, conj (x i) * conj (magneticMatrix A Θ j i) * x j
      = ∑ u, ∑ v, (1 / 2 : ℂ)
          * ((A u v : ℂ) * conj (Complex.exp (Complex.I * (Θ u v : ℂ)))
            * (conj (x v) * x u)) := by
    rw [hc2s]
    simp only [Finset.mul_sum]
  -- assemble
  rw [hdiag, hc1, hc2]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => step1 u v))]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]

/-- The energy identity in real-coerced form: the magnetic quadratic
form *is* the real energy sum, so it is real-valued. -/
theorem magnetic_energy_real (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) (x : V → ℂ) :
    hermQuadForm (magneticLaplacian A Θ) x
      = ↑(∑ u, ∑ v, A u v * Complex.normSq (x u - Complex.exp (Complex.I * Θ u v) * x v) / 2) := by
  have hentry : ∀ u v : V,
      ↑(A u v * Complex.normSq (x u - Complex.exp (Complex.I * Θ u v) * x v) / 2)
        = (A u v : ℂ) * Complex.normSq (x u - Complex.exp (Complex.I * Θ u v) * x v) / 2 := by
    intro u v
    push_cast
    ring
  rw [magnetic_energy, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun v _ => (hentry u v).symm

/-- The magnetic quadratic form is real-valued (the energy identity at
the imaginary coordinate). -/
theorem magneticQuadForm_im_eq_zero (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    (x : V → ℂ) :
    (hermQuadForm (magneticLaplacian A Θ) x).im = 0 := by
  rw [magnetic_energy_real]
  simp

/-- **PSD**: the magnetic Laplacian is positive semidefinite on
nonnegative weights — every edge energy is nonnegative. (The
nonnegativity hypothesis is load-bearing: the QA carries the signed
refutation.) -/
theorem magneticQuadForm_re_nonneg (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    (x : V → ℂ) (hA : ∀ u v, 0 ≤ A u v) :
    0 ≤ (hermQuadForm (magneticLaplacian A Θ) x).re := by
  rw [magnetic_energy_real]
  simp only [Complex.ofReal_re]
  refine Finset.sum_nonneg ?_
  intro u _
  refine Finset.sum_nonneg ?_
  intro v _
  exact div_nonneg (mul_nonneg (hA u v) (Complex.normSq_nonneg _)) (by norm_num)

/-!
## The gauge characterization
-/

/-- **The balanced-potential characterization of the magnetic kernel**:
on nonnegative weights, the magnetic energy vanishes exactly when `x`
is a phase potential aligned with the edge fluxes — `x_u = e^{iΘ_uv} x_v`
on every positive edge. A *frustrated* cycle (nonintegral total flux)
admits no nonzero aligned potential, forcing the form positive definite
— spectral localization of flux at form level, with no eigenvalue
machinery. -/
theorem magneticQuadForm_eq_zero_iff (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    (x : V → ℂ) (hA : ∀ u v, 0 ≤ A u v) :
    hermQuadForm (magneticLaplacian A Θ) x = 0
      ↔ ∀ u v, A u v ≠ 0 → x u = Complex.exp (Complex.I * Θ u v) * x v := by
  have hnonneg : ∀ u' : V, 0 ≤ ∑ v', A u' v' * Complex.normSq
      (x u' - Complex.exp (Complex.I * Θ u' v') * x v') / 2 :=
    fun u' => Finset.sum_nonneg fun v' _ =>
      div_nonneg (mul_nonneg (hA u' v') (Complex.normSq_nonneg _)) (by norm_num)
  rw [magnetic_energy_real]
  constructor
  · intro h u v huv
    have hS : (∑ u', ∑ v', A u' v' * Complex.normSq
        (x u' - Complex.exp (Complex.I * Θ u' v') * x v') / 2) = 0 :=
      Complex.ofReal_eq_zero.1 h
    have hmem := (Finset.sum_eq_zero_iff_of_nonneg (fun u' _ => hnonneg u')).1 hS u
      (Finset.mem_univ u)
    have hmem2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v' _ => div_nonneg (mul_nonneg (hA u v') (Complex.normSq_nonneg _))
        (by norm_num))).1 hmem v (Finset.mem_univ v)
    rcases div_eq_zero_iff.1 hmem2 with h1 | h2
    · rcases mul_eq_zero.1 h1 with h1' | h1'
      · exact absurd h1' huv
      · exact eq_of_sub_eq_zero (Complex.normSq_eq_zero.1 h1')
    · exact absurd h2 (by norm_num)
  · intro h
    refine Complex.ofReal_eq_zero.2
      ((Finset.sum_eq_zero_iff_of_nonneg (fun u' _ => hnonneg u')).mpr ?_)
    intro u _
    refine (Finset.sum_eq_zero_iff_of_nonneg
      (fun v' _ => div_nonneg (mul_nonneg (hA u v') (Complex.normSq_nonneg _))
        (by norm_num))).mpr ?_
    intro v _
    by_cases huv : A u v = 0
    · simp [huv]
    · have hx : x u - Complex.exp (Complex.I * Θ u v) * x v = 0 := by
        have h1 := h u v huv
        simp only [sub_eq_zero]
        exact h1
      have hn : Complex.normSq (x u - Complex.exp (Complex.I * Θ u v) * x v) = 0 := by
        rw [hx, Complex.normSq_zero]
      field_simp [hn]

/-!
## The kernel at the action level

The gauge characterization above is stated at *form* level. This section
promotes it to the kernel (action) level — the interface consumers of
the magnetic kernel theorem need: `M *ᵥ x = 0` iff the potential is
aligned with the edge fluxes. The missing half is pure row algebra at
unit modulus (the phase `e^{iθ}` cancels against its inverse — `exp` is
never zero); the form half is the delivered iff.
-/

omit [DecidableEq V] in
/-- The quadratic form vanishes on the kernel, hypothesis-free: the
form is a pairing with the action. -/
theorem hermQuadForm_eq_zero_of_mulVec_eq_zero (M : Matrix V V ℂ) (x : V → ℂ)
    (h : M *ᵥ x = 0) : hermQuadForm M x = 0 := by
  rw [hermQuadForm, h]
  simp

/-- Conjugate pairing of a unit phase: `conj (e^{i t}) · e^{i t} = 1`,
the finite-algebra unit-modulus fact (the exponential's series
conjugates termwise). -/
theorem conj_exp_I_mul_exp_I (t : ℝ) :
    conj (Complex.exp (Complex.I * (t : ℂ))) * Complex.exp (Complex.I * (t : ℂ))
      = 1 := by
  have h0 : conj (Complex.I * (t : ℂ)) + Complex.I * (t : ℂ) = 0 := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [← Complex.exp_conj, ← Complex.exp_add, h0, Complex.exp_zero]

/-- Every aligned potential is killed by the magnetic Laplacian — pure
row algebra, hypothesis-free on the weights: each row's coupling term
`A uv · e^{iΘuv} · x v` collapses to `A uv · x u` by the alignment
(its inverse), and the conjugate transposed term likewise through the
unit-modulus pairing. -/
theorem magneticLaplacian_mulVec_eq_zero_of_forall_exp_mul_eq
    (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) (x : V → ℂ)
    (halign : ∀ u v, A u v ≠ 0 →
      x u = Complex.exp (Complex.I * (Θ u v : ℂ)) * x v) :
    magneticLaplacian A Θ *ᵥ x = 0 := by
  have h1 : ∀ u : V, ∑ j, magneticMatrix A Θ u j * x j
      = ((outDeg A u : ℝ) : ℂ) * x u := by
    intro u
    have hterm : ∑ j, magneticMatrix A Θ u j * x j
        = ∑ j, ((A u j : ℝ) : ℂ) * x u := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : A u j = 0
      · simp [magneticMatrix, h]
      · simp only [magneticMatrix]
        rw [mul_assoc, ← halign u j h]
    rw [hterm, ← Finset.sum_mul, ← Complex.ofReal_sum]
    rfl
  have h2 : ∀ u : V, ∑ j, conj (magneticMatrix A Θ j u) * x j
      = ((inDeg A u : ℝ) : ℂ) * x u := by
    intro u
    have hterm : ∑ j, conj (magneticMatrix A Θ j u) * x j
        = ∑ j, ((A j u : ℝ) : ℂ) * x u := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : A j u = 0
      · simp [magneticMatrix, h]
      · have hj : x j = Complex.exp (Complex.I * (Θ j u : ℂ)) * x u := halign j u h
        have hu1 := conj_exp_I_mul_exp_I (Θ j u)
        rw [hj, show conj (magneticMatrix A Θ j u)
            = ((A j u : ℝ) : ℂ) * conj (Complex.exp (Complex.I * (Θ j u : ℂ))) from by
            rw [magneticMatrix]; simp only [map_mul, Complex.conj_ofReal]]
        linear_combination ((A j u : ℝ) : ℂ) * x u * hu1
    rw [hterm, ← Finset.sum_mul, ← Complex.ofReal_sum]
    rfl
  funext u
  rw [magneticLaplacian_mulVec_apply, h1 u, h2 u]
  show (((outDeg A u + inDeg A u) / 2 : ℝ) : ℂ) * x u
    - (1 / 2 : ℂ) * (((outDeg A u : ℝ) : ℂ) * x u + ((inDeg A u : ℝ) : ℂ) * x u) = 0
  push_cast
  ring

/-- **The magnetic kernel characterization**: on nonnegative weights,
`M(A, Θ) *ᵥ x = 0` exactly when `x` is a phase potential aligned with
the edge fluxes (`x u = e^{iΘ u v} · x v` on every positive edge). The
delivered form-level gauge iff, promoted to the kernel by the row
algebra above — *spectral localization of flux* at operator level: a
frustrated cycle (nonintegral total flux) forces the kernel trivial.
This is the exact statement shape the signed-graph balance theorem
consumes at the π-flux. -/
theorem magneticLaplacian_mulVec_eq_zero_iff (A : Matrix V V ℝ)
    (Θ : Matrix V V ℝ) (hA : ∀ u v, 0 ≤ A u v) (x : V → ℂ) :
    magneticLaplacian A Θ *ᵥ x = 0
      ↔ ∀ u v, A u v ≠ 0 →
        x u = Complex.exp (Complex.I * (Θ u v : ℂ)) * x v :=
  ⟨fun hker u v huv =>
    (magneticQuadForm_eq_zero_iff A Θ x hA).1
      (hermQuadForm_eq_zero_of_mulVec_eq_zero _ x hker) u v huv,
    magneticLaplacian_mulVec_eq_zero_of_forall_exp_mul_eq A Θ x⟩

/-!
## Cone agreements
-/

/-- At zero phase the magnetic Laplacian degenerates to the entry form
of the complexified classical Laplacian on the symmetrized weights:
the symmetrized degree on the diagonal, half the symmetrized coupling
off it. Loops included, no case analysis. -/
theorem magneticLaplacian_zero_phase_apply (A : Matrix V V ℝ) (u v : V) :
    magneticLaplacian A 0 u v
      = ((if u = v then (outDeg A u + inDeg A u) / 2 else 0)
          - (A u v + A v u) / 2 : ℝ) := by
  classical
  have hE : ∀ w z : V, magneticMatrix A 0 w z = (A w z : ℂ) := by
    intro w z
    simp only [magneticMatrix]
    norm_num
  show ((Matrix.diagonal (fun w => (symDeg A w : ℂ))
      - (1 / 2 : ℂ) • (magneticMatrix A 0 + (magneticMatrix A 0)ᴴ)) u v) = _
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, hE u v, hE v u,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  by_cases huv : u = v
  · simp only [huv, if_pos rfl]
    rw [show symDeg A v = (outDeg A v + inDeg A v) / 2 from rfl]
    push_cast
    ring
  · simp only [huv, if_false, if_neg (fun h : v = u => huv h.symm)]
    push_cast
    ring

/-- On symmetric weights, the zero-phase magnetic Laplacian *is* the
complexified classical Laplacian — the join of the magnetic program
with the real shelf. -/
theorem magneticLaplacian_zero_phase_apply_of_isSymm {A : Matrix V V ℝ}
    (hA : A.IsSymm) (u v : V) :
    magneticLaplacian A 0 u v = ((laplacian A) u v : ℂ) := by
  classical
  have hdeg : ∀ w : V, outDeg A w + inDeg A w = 2 * deg A w := by
    intro w
    have hin : inDeg A w = deg A w := by
      rw [inDeg, deg]
      refine (Finset.sum_congr rfl fun j _ => ?_).symm
      have h1 : (Aᵀ : Matrix V V ℝ) j w = A j w := by rw [hA.eq]
      rw [← h1, Matrix.transpose_apply]
    rw [outDeg_eq_deg, hin]
    ring
  have hent : ∀ w z : V, (A w z + A z w) / 2 = A w z := by
    intro w z
    rw [← hA.apply w z]
    ring
  rw [magneticLaplacian_zero_phase_apply, hdeg u, hent u v]
  by_cases huv : u = v
  · subst huv
    have hpos : (if u = u then 2 * deg A u / 2 else 0) - A u u = deg A u - A u u := by
      rw [if_pos rfl]
      field_simp
    rw [hpos, laplacian, Matrix.sub_apply, degreeMatrix_diagonal]
  · rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal A huv,
      if_neg huv, zero_sub]

/-- On the symmetric/antisymmetric cone the Hermitian part collapses:
the classical single-`W` magnetic Laplacian `D_sym − A∘e^{iΘ}` is
*derived*, not assumed — the definition's directed-native generality
loses nothing on the undirected-with-flux case. -/
theorem magneticLaplacian_eq_single (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    (hA : A.IsSymm) (hΘ : ∀ u v, Θ u v = -Θ v u) :
    magneticLaplacian A Θ
      = Matrix.diagonal (fun u => (symDeg A u : ℂ)) - magneticMatrix A Θ := by
  have hW : (magneticMatrix A Θ)ᴴ = magneticMatrix A Θ :=
    (magneticMatrix_isHermitian A Θ hA hΘ).eq
  rw [magneticLaplacian, hW]
  congr 1
  module

end SpectralGraphTheory
