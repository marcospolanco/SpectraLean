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
import Scaffold.Mathlib.GraphTheory.Magnetic

/-!
# Signed graphs: the balance theorem via the magnetic π-flux bridge

The signed-graph slice of the graph-model axis
(`proposals/signed-graphs-balance.md`, delivered 2026-08-26): the
classical signed Laplacian `L_σ = D − A_σ` at `A_σ := A ∘ σ` with a
`{±1}`-valued signing `σ`, and **Harary balance** in its kernel form —
the strategy's load-bearing-growth principle executed on the magnetic
program: a signing is exactly a magnetic potential at the π-flux
(`e^{iΘ} ∈ {±1}`), so the delivered `magnetic_energy` identity becomes
the signed Dirichlet energy and everything downstream runs through it.

## The objects

* `signedAdj A s` — the entrywise-signed adjacency `A u v * s u v`.
* `signedLaplacian A s` — `degreeMatrix A − signedAdj A s`; at
  `s ≡ 1` this is `laplacian A` entrywise. Symmetric on symmetric `A`
  and symmetric `s` (`signedLaplacian_symmetric`).
* `IsBalanced A s` — a switching exists: `∃ g : V → {±1}, σ_uv =
  g u * g v` on every positive edge (the Harary balance condition).

The signing convention: `s : V → V → ℝ` with explicit hypotheses
`∀ u v, s u v = 1 ∨ s u v = -1` (±1), symmetry, and — on edges of
positive weight — loops are *forced* unsigned by balance itself
(`s u u = g u * g u = 1`), so no separate loop hypothesis is carried:
a negative loop on a positive self-weight simply makes the signing
unbalanced (QA witnesses this boundary).

## The bridge to the magnetic shelf (load-bearing)

`signFlux s u v := if s u v = -1 then π else 0` gives
`e^{i·flux} = s u v` entrywise (`complex_exp_I_mul_signFlux`), and the
join `magneticLaplacian_signFlux_apply` identifies the magnetic
Laplacian at that flux with the complexified signed Laplacian,
entrywise, on symmetric input. The **signed energy identity**
`signedLaplacian_quadForm` is then *derived from the delivered
`magnetic_energy`* — not re-proved: a defect in the magnetic energy
identity would break the signed theorems below. The complex-valued
form (`hermQuadForm_signedLaplacian`) carries the same derivation at
complex test vectors.

## The kernel story

* `signedLaplacian_mulVec_apply` — the row-sum identity
  `(L_σ *ᵥ x) u = ∑ v, A u v * (x u − s u v * x v)`, hypothesis-free.
* `signedLaplacian_mulVec_eq_zero_iff_aligned` — the kernel
  characterization: `L_σ *ᵥ x = 0 ↔ x u = s u v * x v` on every
  positive edge (the energy identity makes → termwise; the row-sum
  makes ←).
* `exists_switching_of_aligned` — the walk collapse: an aligned nonzero
  potential on a connected support graph is a switching function up to
  scale (`supportGraph.Walk` induction, the electrical program's
  `exists_const_of_laplacian_mulVec_eq_zero` pattern with the
  accumulated sign product in place of the constant).

## The headlines

* **`isBalanced_iff_exists_ne_zero_mulVec_eq_zero`** — the Harary
  balance theorem in kernel form: on a connected symmetric nonnegative
  network, `IsBalanced A s ↔ ∃ x ≠ 0, L_σ *ᵥ x = 0`. The forward
  direction is a direct row-sum computation at the switching (no
  connectivity or nonnegativity needed, `exists_mulVec_eq_zero_of_isBalanced`);
  the backward direction runs kernel → alignment → walk collapse.
  Balance is thus *spectral*: a frustrated cycle (nowhere a consistent
  switching) forces the form positive definite
  (`quadForm_pos_of_ne_zero_of_not_isBalanced`).
* **The switching similarity** `diagonal_mul_signedLaplacian_mul_diagonal`:
  at a balanced signing with switching `g`,
  `diag(g) · L_σ · diag(g) = laplacian A` (so `L_σ = diag(g) · L · diag(g)`
  since `g² = 1` entrywise) — the classical "balanced ⟹ spectrally
  unsigned" fact, and eigenpairs transfer at switched vectors
  `g ⊙ v` in both directions (`signedLaplacian_mulVec_switchVec`,
  `laplacian_mulVec_switchVec`), the `Normalized` eigenpair-transfer
  pattern at the involutive diagonal gauge.

## Classical background (route provenance only — all proved here)

- F. Harary, *On the notion of balance of a signed graph*, Michigan
  Math. J. 2 (1953) 143–146 — balance ⟺ switching ⟺ positive cycle
  products.
- T. Zaslavsky, *Signed graphs*, Discrete Appl. Math. 4 (1982) 47–74 —
  the signed Laplacian and switching/spectrum theory.
- The magnetic view of signings (π-flux potentials) is the
  Crucini–Pérez–Bungert–Van Mieghem convention already on the shelf in
  `GraphTheory/Magnetic.lean`.

## Scope

No multiset-level spectrum equality `evals L_σ = evals L` (needs an
eigenvalue-counting argument beyond the ∃-witness transfer — priced
follow-on), no Zaslavsky chromatic/counting theory, no signed Cheeger,
no frustration-index variational theory (the magnetic program's gated
synchronization layer). Everything here is proved; no axiom is
admitted.

QA: `Scaffold/QA/SpectralGraph/Signed_QA.lean` — the balanced and
frustrated fixtures at the theorem instances, the disconnected
conclusion-level fence isolating connectivity, the negative-loop
boundary, the magnetic join pinned on a concrete fixture, and the
switching similarity and eigen-transfer instances at the independently
known path eigenpair.
-/

open scoped BigOperators Matrix ComplexConjugate

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Definitions
-/

/-- The signed adjacency: the entrywise product `A u v * s u v`. At
`s ≡ 1` this is `A` itself. -/
def signedAdj (A : WAdj (V := V)) (s : V → V → ℝ) : WAdj (V := V) :=
  fun u v => A u v * s u v

/-- The **signed Laplacian** `L_σ = D − A_σ` at the matrix convention
matching the shelf's `laplacian A = degreeMatrix A − A`. -/
def signedLaplacian (A : WAdj (V := V)) (s : V → V → ℝ) : WAdj (V := V) :=
  degreeMatrix A - signedAdj A s

omit [Fintype V] [DecidableEq V] in
/-- The signed adjacency is symmetric when both `A` and `s` are. -/
theorem signedAdj_symmetric (A : WAdj (V := V)) (hsymm : ∀ u v, s u v = s v u)
    (hA : A.IsSymm) : (signedAdj A s).IsSymm := by
  refine Matrix.IsSymm.ext fun u v => ?_
  simp only [signedAdj]
  rw [Matrix.IsSymm.apply hA u v, hsymm u v]

/-- The signed Laplacian is symmetric when both `A` and `s` are. -/
theorem signedLaplacian_symmetric (A : WAdj (V := V))
    (hsymm : ∀ u v, s u v = s v u) (hA : A.IsSymm) :
    (signedLaplacian A s).IsSymm :=
  (degreeMatrix_symmetric A).sub (signedAdj_symmetric A hsymm hA)

/-- **Harary balance**: a switching exists — a `{±1}`-valued vertex
function `g` with `s u v = g u * g v` on every edge of positive
weight. On positive self-weights this forces loops unsigned
(`g u * g u = 1`), so the definition needs no separate loop
convention. -/
def IsBalanced (A : WAdj (V := V)) (s : V → V → ℝ) : Prop :=
  ∃ g : V → ℝ, (∀ v, g v = 1 ∨ g v = -1) ∧
    ∀ u v, A u v ≠ 0 → s u v = g u * g v

/-!
## The magnetic π-flux bridge
-/

/-- The magnetic potential of a signing: flux `π` exactly on the
negative entries, `0` on the positive ones — `e^{i·flux} = s u v`
entrywise. -/
noncomputable def signFlux (s : V → V → ℝ) : Matrix V V ℝ :=
  fun u v => if s u v = -1 then Real.pi else 0

omit [Fintype V] [DecidableEq V] in
/-- The phase of the signing's flux is the sign: `e^{i·signFlux} = s`,
entrywise, at the `±1` constraint. -/
theorem complex_exp_I_mul_signFlux {s : V → V → ℝ}
    (hs : ∀ u v, s u v = 1 ∨ s u v = -1) (u v : V) :
    Complex.exp (Complex.I * (signFlux s u v : ℂ)) = (s u v : ℂ) := by
  rcases hs u v with h | h
  · have hf : signFlux s u v = 0 := by
      simp only [signFlux]
      rw [if_neg]
      intro hcon
      rw [hcon] at h
      norm_num at h
    simp [hf, h]
  · have hf : signFlux s u v = Real.pi := by
      simp only [signFlux, if_pos h]
    rw [hf]
    rw [show Complex.I * ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) * Complex.I by ring]
    rw [Complex.exp_mul_I]
    simp [Real.cos_pi, Real.sin_pi, h]

omit [DecidableEq V] in
/-- The symmetrized degree is the degree on the symmetric cone. -/
theorem symDeg_eq_deg {A : WAdj (V := V)} (hA : A.IsSymm) (u : V) :
    symDeg A u = deg A u := by
  have hin : inDeg A u = deg A u := by
    rw [inDeg, deg]
    refine (Finset.sum_congr rfl fun j _ => ?_).symm
    have h1 : (Aᵀ : Matrix V V ℝ) j u = A j u := by rw [hA.eq]
    rw [← h1, Matrix.transpose_apply]
  rw [symDeg, outDeg_eq_deg, hin]
  ring

/-- **The join with the magnetic shelf, entrywise**: on symmetric `A`
and symmetric `s`, the magnetic Laplacian at the signing's flux *is*
the complexified signed Laplacian. The signed program's every
spectral statement routes through this identification. -/
theorem magneticLaplacian_signFlux_apply {A : WAdj (V := V)} {s : V → V → ℝ}
    (hA : A.IsSymm) (hsymm : ∀ u v, s u v = s v u)
    (hs : ∀ u v, s u v = 1 ∨ s u v = -1) (u v : V) :
    magneticLaplacian A (signFlux s) u v = ((signedLaplacian A s) u v : ℂ) := by
  classical
  have hW : ∀ w z : V, magneticMatrix A (signFlux s) w z
      = (signedAdj A s w z : ℂ) := by
    intro w z
    simp only [magneticMatrix, signedAdj]
    rw [complex_exp_I_mul_signFlux hs, Complex.ofReal_mul]
  have hWstar : ∀ w z : V, star (magneticMatrix A (signFlux s) w z)
      = (signedAdj A s w z : ℂ) := by
    intro w z
    rw [Complex.star_def, hW w z, Complex.conj_ofReal]
  have hsA : ∀ w z : V, signedAdj A s w z = signedAdj A s z w := by
    intro w z
    simp only [signedAdj]
    rw [Matrix.IsSymm.apply hA w z, hsymm w z]
  rw [magneticLaplacian, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    hW u v, hWstar v u, hsA v u, signedLaplacian, Matrix.sub_apply, signedAdj,
    Complex.ofReal_sub]
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl, degreeMatrix_diagonal, symDeg_eq_deg hA u]
    push_cast
    ring
  · rw [if_neg huv, degreeMatrix_off_diagonal A huv]
    push_cast
    ring

omit [DecidableEq V] in
/-- The complex quadratic form at coerced real data is the coerced real
form — the bridge the real energy identity crosses. -/
theorem hermQuadForm_map_ofReal {M : WAdj (V := V)} {x : V → ℝ} :
    hermQuadForm (fun u v => (M u v : ℂ)) (fun u => (x u : ℂ))
      = ((quadForm M x) : ℂ) := by
  simp only [hermQuadForm, Matrix.mulVec, Matrix.dotProduct, quadForm,
    map_mul, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_sum]

/-- **The signed energy identity at complex test vectors**, derived
from the delivered `magnetic_energy` through the π-flux join: the
complexified signed Laplacian's form measures the signed disagreement
`|y u − s u v · y v|²` along (ordered) edge pairs. This is the
load-bearing consumption of the magnetic energy identity: a wrong
`magnetic_energy` breaks this theorem. -/
theorem hermQuadForm_signedLaplacian {A : WAdj (V := V)} {s : V → V → ℝ}
    (hA : A.IsSymm) (hsymm : ∀ u v, s u v = s v u)
    (hs : ∀ u v, s u v = 1 ∨ s u v = -1) (y : V → ℂ) :
    hermQuadForm (fun u v => ((signedLaplacian A s) u v : ℂ)) y
      = ∑ u, ∑ v, (A u v : ℂ) * Complex.normSq (y u - (s u v : ℂ) * y v) / 2 := by
  have key : hermQuadForm (fun u v => ((signedLaplacian A s) u v : ℂ)) y
      = hermQuadForm (magneticLaplacian A (signFlux s)) y := by
    simp only [hermQuadForm, Matrix.mulVec, Matrix.dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine congrArg (fun t : ℂ => conj (y i) * t) ?_
    exact Finset.sum_congr rfl fun j _ => by
      rw [magneticLaplacian_signFlux_apply hA hsymm hs i j]
  rw [key, magnetic_energy]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [complex_exp_I_mul_signFlux hs]

/-- **The signed Dirichlet energy identity** (real form): `xᵀL_σ x =
½ ∑ A u v (x u − s u v x v)²`, obtained from the complex identity at
coerced test vectors. The kernel story below consumes exactly this. -/
theorem signedLaplacian_quadForm {A : WAdj (V := V)} {s : V → V → ℝ}
    (hA : A.IsSymm) (hsymm : ∀ u v, s u v = s v u)
    (hs : ∀ u v, s u v = 1 ∨ s u v = -1) (x : V → ℝ) :
    quadForm (signedLaplacian A s) x
      = ∑ u, ∑ v, A u v * (x u - s u v * x v) ^ 2 / 2 := by
  have key := hermQuadForm_signedLaplacian hA hsymm hs (fun u => (x u : ℂ))
  rw [hermQuadForm_map_ofReal] at key
  have hnorm : ∀ u v : V, (A u v : ℂ) * Complex.normSq
      ((x u : ℂ) - (s u v : ℂ) * (x v : ℂ)) / 2
      = ((A u v * (x u - s u v * x v) ^ 2 / 2 : ℝ) : ℂ) := by
    intro u v
    have hsub : ((x u : ℂ) - (s u v : ℂ) * (x v : ℂ))
        = ((x u - s u v * x v : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, Complex.normSq_ofReal]
    push_cast
    ring
  have hsum : ∑ u, ∑ v, (A u v : ℂ) * Complex.normSq
      ((x u : ℂ) - (s u v : ℂ) * (x v : ℂ)) / 2
      = ((∑ u, ∑ v, A u v * (x u - s u v * x v) ^ 2 / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    exact Finset.sum_congr rfl fun v _ => hnorm u v
  exact Complex.ofReal_inj.1 (key.trans hsum)

/-!
## The kernel story
-/

/-- **The row-sum identity**: `(L_σ *ᵥ x) u = ∑ v, A u v (x u − s u v x v)`,
hypothesis-free — the workhorse behind both the balanced-to-kernel
computation and the aligned-to-kernel half of the characterization. -/
theorem signedLaplacian_mulVec_apply {A : WAdj (V := V)} {s : V → V → ℝ}
    (x : V → ℝ) (u : V) :
    (signedLaplacian A s *ᵥ x) u = ∑ v, A u v * (x u - s u v * x v) := by
  have h1 : ∑ v, degreeMatrix A u v * x v = ∑ v, A u v * x u := by
    have hsingle : ∑ v, degreeMatrix A u v * x v = degreeMatrix A u u * x u :=
      Finset.sum_eq_single u
        (fun b _ hb => by rw [degreeMatrix_off_diagonal A (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_univ u) h)
    rw [hsingle, degreeMatrix_diagonal, ← Finset.sum_mul]
    rfl
  have h2 : (signedLaplacian A s *ᵥ x) u
      = ∑ v, degreeMatrix A u v * x v - ∑ v, A u v * s u v * x v := by
    simp only [Matrix.mulVec, Matrix.dotProduct, signedLaplacian,
      Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, signedAdj]
  rw [h2, h1, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- **The kernel characterization**: on symmetric nonnegative weights,
the signed Laplacian kills `x` exactly when `x` is aligned with the
signs (`x u = s u v x v` on every positive edge). The forward half is
the energy identity made termwise; the backward half is the row-sum
identity at aligned potentials. -/
theorem signedLaplacian_mulVec_eq_zero_iff_aligned {A : WAdj (V := V)}
    {s : V → V → ℝ} (hA : A.IsSymm) (hnn : ∀ u v, 0 ≤ A u v)
    (hsymm : ∀ u v, s u v = s v u) (hs : ∀ u v, s u v = 1 ∨ s u v = -1)
    (x : V → ℝ) :
    signedLaplacian A s *ᵥ x = 0
      ↔ ∀ u v, A u v ≠ 0 → x u = s u v * x v := by
  constructor
  · intro hker
    have hq : quadForm (signedLaplacian A s) x = 0 := by
      simp only [quadForm, Matrix.dotProduct, hker, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero]
    rw [signedLaplacian_quadForm hA hsymm hs] at hq
    have hnonneg : ∀ u' : V, 0 ≤ ∑ v', A u' v' * (x u' - s u' v' * x v') ^ 2 / 2 :=
      fun u' => Finset.sum_nonneg fun v' _ =>
        div_nonneg (mul_nonneg (hnn u' v') (sq_nonneg _)) (by norm_num)
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg
      (fun u' _ => hnonneg u')).1 hq
    intro u v huv
    have hmem := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v' _ => div_nonneg (mul_nonneg (hnn u v') (sq_nonneg _)) (by norm_num))).1
      (hsum u (Finset.mem_univ u)) v (Finset.mem_univ v)
    rcases div_eq_zero_iff.1 hmem with h1 | h2
    · rcases mul_eq_zero.1 h1 with h1' | h1'
      · exact absurd h1' huv
      · exact eq_of_sub_eq_zero (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1')
    · exact absurd h2 (by norm_num)
  · intro halign
    funext u
    rw [signedLaplacian_mulVec_apply]
    refine Finset.sum_eq_zero ?_
    intro v _
    by_cases h : A u v = 0
    · rw [h, zero_mul]
    · rw [halign u v h]
      ring

/-!
## The walk collapse
-/

omit [Fintype V] [DecidableEq V] in
/-- A walk across the support graph multiplies a potential by a `±1`
accumulated sign: the alignment propagation underlying the collapse.
Induction over `SimpleGraph.Walk`, the electrical program's
`eq_of_supportGraph_walk` pattern with the sign product in place of
the constant. -/
theorem walk_sign {A : WAdj (V := V)} {s : V → V → ℝ} (hA : A.IsSymm)
    (hs : ∀ u v, s u v = 1 ∨ s u v = -1) {x : V → ℝ}
    (halign : ∀ u v, A u v ≠ 0 → x u = s u v * x v) {i j : V}
    (w : (supportGraph A hA).Walk i j) :
    ∃ r : ℝ, (r = 1 ∨ r = -1) ∧ x j = r * x i := by
  induction w with
  | nil => exact ⟨1, Or.inl rfl, (one_mul _).symm⟩
  | cons hadj rest ih =>
    rename_i vstart nbr vend
    obtain ⟨r', hr', hxr'⟩ := ih
    obtain ⟨_, hpos⟩ := supportGraph_adj.1 hadj
    have hsq : s vstart nbr * s vstart nbr = 1 := by
      rcases hs vstart nbr with h | h <;> rw [h] <;> norm_num
    have hkr : x nbr = s vstart nbr * x vstart := by
      calc x nbr = s vstart nbr * s vstart nbr * x nbr := by rw [hsq, one_mul]
        _ = s vstart nbr * (s vstart nbr * x nbr) := by ring
        _ = s vstart nbr * x vstart := by rw [← halign vstart nbr hpos.ne']
    refine ⟨r' * s vstart nbr, ?_, ?_⟩
    · rcases hr' with h | h <;> rcases hs vstart nbr with h' | h' <;>
        rw [h, h'] <;> norm_num
    · rw [hxr', hkr]; ring

omit [DecidableEq V] in
/-- **The walk collapse**: an aligned nonzero potential on a connected
support graph is a switching function up to scale — every entry is
`c • g` with `g : V → {±1}` and `c ≠ 0`. This is the signed analogue
of `exists_const_of_laplacian_mulVec_eq_zero` (the constant line
becomes the switching orbit). -/
theorem exists_switching_of_aligned {A : WAdj (V := V)} {s : V → V → ℝ}
    (hA : A.IsSymm) (hs : ∀ u v, s u v = 1 ∨ s u v = -1)
    (hconn : (supportGraph A hA).Connected) {x : V → ℝ} (hx : x ≠ 0)
    (halign : ∀ u v, A u v ≠ 0 → x u = s u v * x v) :
    ∃ (g : V → ℝ) (c : ℝ), (∀ v, g v = 1 ∨ g v = -1) ∧ c ≠ 0 ∧
      ∀ v, x v = c * g v := by
  obtain ⟨u₀, hu₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx (funext hcon)
  refine ⟨fun v => x v / x u₀, x u₀, ?_, hu₀, fun v => by field_simp⟩
  intro v
  obtain ⟨w⟩ := hconn u₀ v
  obtain ⟨r, hr, hxr⟩ := walk_sign hA hs halign w
  rcases hr with h | h
  · left; show x v / x u₀ = 1; rw [hxr, h]; field_simp
  · right; show x v / x u₀ = -1; rw [hxr, h]; field_simp

/-!
## The balance theorem
-/

/-- **Balance gives a kernel vector**: the switching itself is killed
by the signed Laplacian — a direct row-sum computation, hypothesis-free
on connectivity and nonnegativity. Requires the vertex type inhabited
(the switching must be nonzero). -/
theorem exists_mulVec_eq_zero_of_isBalanced {A : WAdj (V := V)} {s : V → V → ℝ}
    [Nonempty V] (hbal : IsBalanced A s) :
    ∃ x : V → ℝ, x ≠ 0 ∧ signedLaplacian A s *ᵥ x = 0 := by
  obtain ⟨g, hgpm, hgs⟩ := hbal
  obtain ⟨w⟩ := ‹Nonempty V›
  refine ⟨g, ?_, ?_⟩
  · intro h
    have h0 : g w = 0 := by rw [h]; rfl
    rcases hgpm w with h' | h' <;> rw [h'] at h0 <;> norm_num at h0
  · funext u
    rw [signedLaplacian_mulVec_apply]
    refine Finset.sum_eq_zero ?_
    intro v _
    by_cases h : A u v = 0
    · rw [h, zero_mul]
    · rw [hgs u v h]
      have hu2 : g u * g u = 1 := by
        rcases hgpm u with h | h <;> rw [h] <;> norm_num
      have hv2 : g v * g v = 1 := by
        rcases hgpm v with h | h <;> rw [h] <;> norm_num
      have key : g u - g u * g v * g v = 0 := by
        linear_combination (-(g u)) * hv2
      rw [key, mul_zero]

/-- **A kernel vector gives balance**: on a connected symmetric
nonnegative network, a nonzero vector killed by the signed Laplacian
supplies a `{±1}` switching — kernel → alignment → the walk collapse,
with the scale cancelled against the nonzero anchor. -/
theorem isBalanced_of_mulVec_eq_zero {A : WAdj (V := V)} {s : V → V → ℝ}
    (hA : A.IsSymm) (hnn : ∀ u v, 0 ≤ A u v) (hsymm : ∀ u v, s u v = s v u)
    (hs : ∀ u v, s u v = 1 ∨ s u v = -1)
    (hconn : (supportGraph A hA).Connected) {x : V → ℝ} (hx : x ≠ 0)
    (hker : signedLaplacian A s *ᵥ x = 0) : IsBalanced A s := by
  have halign := (signedLaplacian_mulVec_eq_zero_iff_aligned hA hnn hsymm hs x).1 hker
  obtain ⟨g, c, hgpm, hc, hxc⟩ := exists_switching_of_aligned hA hs hconn hx halign
  refine ⟨g, hgpm, fun u v huv => ?_⟩
  have h1 : c * g u = s u v * (c * g v) := by
    rw [← hxc u, ← hxc v]
    exact halign u v huv
  have h2 : g u = s u v * g v := by
    have h3 : c * g u = c * (s u v * g v) := by rw [h1]; ring
    exact mul_left_cancel₀ hc h3
  have hv2 : g v * g v = 1 := by
    rcases hgpm v with h | h <;> rw [h] <;> norm_num
  rw [h2, show s u v * g v * g v = s u v * (g v * g v) from by ring, hv2,
    mul_one]

/-- **The Harary balance theorem, kernel form** — the headline: on a
connected symmetric nonnegative network with a `{±1}` symmetric
signing, balance *is* the nontriviality of the signed Laplacian's
kernel. Balance is spectral: a frustrated cycle (no consistent
switching) forces the kernel trivial. -/
theorem isBalanced_iff_exists_ne_zero_mulVec_eq_zero {A : WAdj (V := V)}
    {s : V → V → ℝ} (hA : A.IsSymm) (hnn : ∀ u v, 0 ≤ A u v)
    (hsymm : ∀ u v, s u v = s v u) (hs : ∀ u v, s u v = 1 ∨ s u v = -1)
    (hconn : (supportGraph A hA).Connected) :
    IsBalanced A s ↔ ∃ x : V → ℝ, x ≠ 0 ∧ signedLaplacian A s *ᵥ x = 0 :=
  ⟨fun hbal => by
      haveI : Nonempty V := hconn.nonempty
      exact exists_mulVec_eq_zero_of_isBalanced hbal,
    fun ⟨x, hx, hker⟩ => isBalanced_of_mulVec_eq_zero hA hnn hsymm hs hconn hx hker⟩

/-- **Frustration is positive definiteness**: on a connected network
with an unbalanced signing, the signed Dirichlet energy is strictly
positive on every nonzero potential — the form-level spectral
localization of frustration. -/
theorem quadForm_pos_of_ne_zero_of_not_isBalanced {A : WAdj (V := V)}
    {s : V → V → ℝ} (hA : A.IsSymm) (hnn : ∀ u v, 0 ≤ A u v)
    (hsymm : ∀ u v, s u v = s v u) (hs : ∀ u v, s u v = 1 ∨ s u v = -1)
    (hconn : (supportGraph A hA).Connected) (hnb : ¬ IsBalanced A s)
    {x : V → ℝ} (hx : x ≠ 0) : 0 < quadForm (signedLaplacian A s) x := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [signedLaplacian_quadForm hA hsymm hs]
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      div_nonneg (mul_nonneg (hnn u v) (sq_nonneg _)) (by norm_num)
  · intro hzero
    have hqe : quadForm (signedLaplacian A s) x = 0 := hzero.symm
    apply hnb
    have halign : ∀ u v, A u v ≠ 0 → x u = s u v * x v := by
      intro u v huv
      have hnonneg : ∀ u' : V, 0 ≤ ∑ v', A u' v' * (x u' - s u' v' * x v') ^ 2 / 2 :=
        fun u' => Finset.sum_nonneg fun v' _ =>
          div_nonneg (mul_nonneg (hnn u' v') (sq_nonneg _)) (by norm_num)
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg
        (fun u' _ => hnonneg u')).1
        (by rw [← signedLaplacian_quadForm hA hsymm hs]; exact hqe)
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg
        (fun v' _ => div_nonneg (mul_nonneg (hnn u v') (sq_nonneg _))
          (by norm_num))).1 (hsum u (Finset.mem_univ u)) v (Finset.mem_univ v)
      rcases div_eq_zero_iff.1 hmem with h1 | h2
      · rcases mul_eq_zero.1 h1 with h1' | h1'
        · exact absurd h1' huv
        · exact eq_of_sub_eq_zero (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1')
      · exact absurd h2 (by norm_num)
    exact isBalanced_of_mulVec_eq_zero hA hnn hsymm hs hconn hx
      ((signedLaplacian_mulVec_eq_zero_iff_aligned hA hnn hsymm hs x).2 halign)

/-!
## The switching similarity
-/

/-- Entry action of the diagonal sandwich: `(diag(g) · M · diag(g)) u v
= g u * M u v * g v` for any matrix `M`. -/
private theorem diagonal_mul_mul_diagonal_apply (g : V → ℝ) (M : Matrix V V ℝ)
    (u v : V) :
    (Matrix.diagonal g * M * Matrix.diagonal g) u v = g u * M u v * g v := by
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **The switching similarity**: at a balanced signing with switching
`g`, conjugating by the diagonal `g` recovers the unsigned Laplacian —
`diag(g) · L_σ · diag(g) = laplacian A`. Off every positive edge the
switching cancels the sign (`g u σ u v g v = 1`); diagonally `g² = 1`.
The classical "balanced ⟹ spectrally unsigned" fact, at matrix level. -/
theorem diagonal_mul_signedLaplacian_mul_diagonal {A : WAdj (V := V)}
    {s : V → V → ℝ} {g : V → ℝ} (hgpm : ∀ v, g v = 1 ∨ g v = -1)
    (hgs : ∀ u v, A u v ≠ 0 → s u v = g u * g v) :
    Matrix.diagonal g * signedLaplacian A s * Matrix.diagonal g = laplacian A := by
  apply Matrix.ext
  intro u v
  have hu2 : g u * g u = 1 := by rcases hgpm u with h | h <;> rw [h] <;> norm_num
  have hv2 : g v * g v = 1 := by rcases hgpm v with h | h <;> rw [h] <;> norm_num
  have hgsq : (g u * g v) * (g u * g v) = 1 := by
    rw [show (g u * g v) * (g u * g v) = (g u * g u) * (g v * g v) from by ring,
      hu2, hv2, one_mul]
  have hL : (Matrix.diagonal g * signedLaplacian A s * Matrix.diagonal g) u v
      = g u * (degreeMatrix A u v - A u v * s u v) * g v := by
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, signedLaplacian,
      Matrix.sub_apply, signedAdj]
  have hR : laplacian A u v = degreeMatrix A u v - A u v := by
    simp only [laplacian, Matrix.sub_apply]
  rw [hL, hR]
  by_cases huv : u = v
  · subst huv
    by_cases h : A u u = 0
    · rw [h, zero_mul]
      linear_combination (degreeMatrix A u u) * hu2
    · rw [hgs u u h]
      linear_combination (degreeMatrix A u u - A u u * (g u * g u + 1)) * hu2
  · rw [degreeMatrix_off_diagonal A huv, zero_sub, zero_sub]
    by_cases h : A u v = 0
    · simp [h]
    · rw [hgs u v h]
      linear_combination (-(A u v)) * hgsq

/-- The diagonal switching matrix is involutive (`g² = 1` entrywise):
conjugating twice is the identity. -/
theorem diagonal_mul_diagonal_of_sign {g : V → ℝ} (hgpm : ∀ v, g v = 1 ∨ g v = -1) :
    Matrix.diagonal g * Matrix.diagonal g = 1 := by
  apply Matrix.ext
  intro u v
  have hu2 : g u * g u = 1 := by rcases hgpm u with h | h <;> rw [h] <;> norm_num
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl, if_pos rfl, hu2]
  · rw [if_neg huv, if_neg huv]

/-- The switched vector `diag(g) *ᵥ v`, computed entrywise: `g ⊙ v`. -/
theorem switchVec_apply {g : V → ℝ} (v : V → ℝ) (i : V) :
    (Matrix.diagonal g *ᵥ v) i = g i * v i := Matrix.mulVec_diagonal g v i

/-- Switching twice is the identity — the cancellation behind both
eigenpair-transfer directions. -/
theorem switchVec_mulVec_switchVec {g : V → ℝ}
    (hgpm : ∀ v, g v = 1 ∨ g v = -1) (v : V → ℝ) :
    Matrix.diagonal g *ᵥ (Matrix.diagonal g *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, diagonal_mul_diagonal_of_sign hgpm, Matrix.one_mulVec]

/-- Switching preserves nonvanishing (invertible action). -/
theorem switchVec_ne_zero {g : V → ℝ} (hgpm : ∀ v, g v = 1 ∨ g v = -1)
    {v : V → ℝ} (hv : v ≠ 0) : Matrix.diagonal g *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have hc := switchVec_mulVec_switchVec hgpm v
  rw [← hc, h, Matrix.mulVec_zero]

/-- The similarity in conjugated form: `L_σ = diag(g) · laplacian A ·
diag(g)` — the same entry computation with the roles of `L_σ` and `L`
swapped, via the involutivity `g² = 1`. -/
theorem signedLaplacian_eq_diagonal_mul_laplacian_mul_diagonal
    {A : WAdj (V := V)} {s : V → V → ℝ} {g : V → ℝ}
    (hgpm : ∀ v, g v = 1 ∨ g v = -1)
    (hgs : ∀ u v, A u v ≠ 0 → s u v = g u * g v) :
    signedLaplacian A s
      = Matrix.diagonal g * laplacian A * Matrix.diagonal g := by
  apply Matrix.ext
  intro u v
  have hu2 : g u * g u = 1 := by rcases hgpm u with h | h <;> rw [h] <;> norm_num
  have hv2 : g v * g v = 1 := by rcases hgpm v with h | h <;> rw [h] <;> norm_num
  rw [diagonal_mul_mul_diagonal_apply g (laplacian A) u v, laplacian,
    Matrix.sub_apply, signedLaplacian, Matrix.sub_apply, signedAdj]
  by_cases huv : u = v
  · subst huv
    rw [degreeMatrix_diagonal]
    by_cases h : A u u = 0
    · rw [h, zero_mul, sub_zero]
      linear_combination (-(deg A u)) * hu2
    · rw [hgs u u h, hu2]
      linear_combination (-(deg A u - A u u)) * hu2
  · rw [degreeMatrix_off_diagonal A huv]
    by_cases h : A u v = 0
    · simp [h]
    · rw [hgs u v h]
      ring

/-- **Eigenpair transfer, forward**: every eigenpair of the unsigned
Laplacian switches to an eigenpair of the signed Laplacian at the
*same* eigenvalue — the similarity conjugation, with the interior
switch cancelled by involutivity. -/
theorem signedLaplacian_mulVec_switchVec {A : WAdj (V := V)} {s : V → V → ℝ}
    {g : V → ℝ} (hgpm : ∀ v, g v = 1 ∨ g v = -1)
    (hgs : ∀ u v, A u v ≠ 0 → s u v = g u * g v)
    {v : V → ℝ} {μ : ℝ} (hv : laplacian A *ᵥ v = μ • v) :
    signedLaplacian A s *ᵥ (Matrix.diagonal g *ᵥ v)
      = μ • (Matrix.diagonal g *ᵥ v) := by
  have e2 : signedLaplacian A s *ᵥ (Matrix.diagonal g *ᵥ v)
      = Matrix.diagonal g *ᵥ (laplacian A *ᵥ
          (Matrix.diagonal g *ᵥ (Matrix.diagonal g *ᵥ v))) := by
    rw [signedLaplacian_eq_diagonal_mul_laplacian_mul_diagonal hgpm hgs,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e3 : laplacian A *ᵥ (Matrix.diagonal g *ᵥ (Matrix.diagonal g *ᵥ v))
      = laplacian A *ᵥ v :=
    congrArg (Matrix.mulVec (laplacian A)) (switchVec_mulVec_switchVec hgpm v)
  rw [e2, e3, hv, Matrix.mulVec_smul_assoc]

/-- **Eigenpair transfer, backward**: every eigenpair of the signed
Laplacian switches back to an eigenpair of the unsigned Laplacian at
the same eigenvalue — the two-way spectral bridge of the balance
similarity. -/
theorem laplacian_mulVec_switchVec {A : WAdj (V := V)} {s : V → V → ℝ}
    {g : V → ℝ} (hgpm : ∀ v, g v = 1 ∨ g v = -1)
    (hgs : ∀ u v, A u v ≠ 0 → s u v = g u * g v)
    {w : V → ℝ} {μ : ℝ} (hw : signedLaplacian A s *ᵥ w = μ • w) :
    laplacian A *ᵥ (Matrix.diagonal g *ᵥ w)
      = μ • (Matrix.diagonal g *ᵥ w) := by
  have e2 : laplacian A *ᵥ (Matrix.diagonal g *ᵥ w)
      = Matrix.diagonal g *ᵥ (signedLaplacian A s *ᵥ
          (Matrix.diagonal g *ᵥ (Matrix.diagonal g *ᵥ w))) := by
    rw [← diagonal_mul_signedLaplacian_mul_diagonal hgpm hgs,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e3 : signedLaplacian A s *ᵥ (Matrix.diagonal g *ᵥ (Matrix.diagonal g *ᵥ w))
      = signedLaplacian A s *ᵥ w :=
    congrArg (Matrix.mulVec (signedLaplacian A s))
      (switchVec_mulVec_switchVec hgpm w)
  rw [e2, e3, hw, Matrix.mulVec_smul_assoc]

end SpectralGraphTheory
