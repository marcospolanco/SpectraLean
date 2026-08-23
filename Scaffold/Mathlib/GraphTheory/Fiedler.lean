import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.Cheeger

/-!
# The Fiedler vector and its sign partition

Phase A of `proposals/fiedler-partitioning.md`: the Fiedler-vector
interface — existence, the eigenvector equation, and the induced
sign-pattern bipartition with its nonempty/proper sanity facts. This
module is pure hard crust: every declaration is proved, and no axiom is
admitted.

Delivered statements:

- `fiedlerIndex`/`fiedlerVector`: an eigenbasis index carrying the
  second sorted Laplacian eigenvalue, and the eigenvector there
  (`fiedlerVector_eigen`, `fiedlerVector_quadForm`,
  `fiedlerVector_norm`, `fiedlerVector_ne_zero`). Statement difference
  from the proposal sketch, recorded before stating: the sketch wrote
  `eigvecOf (laplacian A) hL ⟨1, by omega⟩`, but `eigvecOf` is indexed
  by `V`, not by the sorted-spectrum positions, so the second-smallest
  eigenvalue must first be located in the eigenbasis listing
  (`evals_mem_eigvalOf`) and the index fixed by classical choice.
- `lambda2_pos_of_connected`: on a connected graph with symmetric
  nonnegative weights, `0 < lambda2` — Fiedler's algebraic-connectivity
  certificate, consuming `laplacian_kernel_eq_span_onesVec` (the
  electrical program's step 2) together with the PSD bound and the
  multiplicity pins. The contrapositive is what makes `lambda2 > 0` the
  right hypothesis for partition sanity: on a disconnected graph the
  kernel is at least two-dimensional and the second sorted eigenvalue
  vanishes.
- `fiedlerPartition`: the standard sign-pattern half-space
  `{i | 0 ≤ fiedlerVector i}`, with `fiedlerPartition_nonempty` and
  `fiedlerPartition_ne_univ` on connected graphs — the partition is a
  genuine bipartition, not a degenerate one. Both sanity facts flow
  through orthogonality to `onesVec` (`fiedlerVector_sum_eq_zero`),
  which is exactly where `lambda2 > 0` is load-bearing: at `lambda2 = 0`
  the eigenvector can be a kernel vector (e.g. `onesVec` itself) whose
  positive set is everything.

Phase B (a certified conductance bound, delivered 2026-08-23 in the
"Phase B" section below) is the classical **Cheeger cut-existence
corollary**: on every connected `d`-regular graph there is a nonempty
proper `S` with `conductance S ^ 2 ≤ 2 * lambda2 / d`, assembled from
the proved Cheeger sweep lemma and `cheegerConstant_attained`. It is
pure hard crust — the proposal's original gate ("run against the
admitted Cheeger hard direction, or defer until it is proved") was
dissolved by the hard direction's retirement on 2026-08-23. Statement
difference from the proposal's Phase B sketch, recorded before stating:
the sketch wrote `conductance (fiedlerPartition …) ≤ [bound]` — the
*sign* half-space — but the Cheeger inequalities bound the conductance
*minimum*, and no λ₂-only upper bound on the sign cut's conductance
holds in general (certifying a specific Fiedler *level set* — the
sweep-extraction statement — is a strictly stronger, separately scoped
follow-on). The delivered existential certificate is over the
conductance minimizer, with the bound running through the Fiedler
vector's Rayleigh quotient.

QA: `Scaffold/QA/SpectralGraph/Fiedler_QA.lean` — the `K₂` fixture
(partition pinned to one of the two singleton halves through the
eigenvector equation, boundary computed), the `P₄` barbell fixture
(two near-cliques joined by a bridge: `lambda2 ≤ 1` through the proved
Rayleigh engine, the eigen equations forcing the sign pattern, and the
partition computed to be exactly the known good cut `{0, 1}` or its
complement, with boundary `1` and volume `3`), and the disconnected
negative witness (the connectivity/`lambda2 > 0` hypothesis shown
load-bearing: `lambda2 = 0` and `onesVec` is a nonzero eigenvector
there whose sign filter is all of `univ`). The Phase B section adds the
`K₂` certificate witnesses: `lambda2 (K₂) = 2` pinned through the
`1 • L_sym = L` scaling bridge to the independently pinned
normalized-Laplacian eigenvalue, the Rayleigh transfer cross-checked
against that pin, the attainment instantiation, the identified cut, and
the regularity refutation (`d = 100`).
-/

open scoped Classical Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The dot product of two scalar multiples of `onesVec` is the scalar
product times the vertex count. Private helper for
`lambda2_pos_of_connected`. -/
private theorem dotProduct_smul_onesVec (c d : ℝ) :
    Matrix.dotProduct (c • onesVec (V := V)) (d • onesVec)
      = (Fintype.card V : ℝ) * (c * d) := by
  simp [Matrix.dotProduct, onesVec, Finset.sum_const]

/-!
## A1: the Fiedler vector
-/

/-- An eigenbasis index whose eigenvalue is the second sorted Laplacian
eigenvalue. Exists by `evals_mem_eigvalOf` (sorting a multiset permutes
it); fixed by classical choice. The cardinality hypothesis keeps the
sorted-spectrum position `1` admissible. -/
noncomputable def fiedlerIndex (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) : V :=
  Classical.choose
    (evals_mem_eigvalOf (laplacian_symmetric A hA) ⟨1, by omega⟩)

/-- Interface to the index choice: the chosen index's eigenvalue *is*
`lambda2`. -/
theorem fiedlerIndex_eigvalOf (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) :
    eigvalOf (laplacian A) (laplacian_symmetric A hA) (fiedlerIndex A hA hcard)
      = lambda2 A hA hcard :=
  (Classical.choose_spec
    (evals_mem_eigvalOf (laplacian_symmetric A hA) ⟨1, by omega⟩)).symm

/-- The Fiedler vector of a symmetric weighted graph: the (unit)
eigenvector of the combinatorial Laplacian at the index carrying
`lambda2`, from the proved orthonormal eigenbasis. Noncomputable
because the eigenbasis and the index choice both come from the spectral
theorem plus classical choice. -/
noncomputable def fiedlerVector (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) : V → ℝ :=
  eigvecOf (laplacian A) (laplacian_symmetric A hA) (fiedlerIndex A hA hcard)

/-- **A1, the eigenvector equation.** The Fiedler vector is a genuine
eigenvector of the Laplacian at eigenvalue `lambda2`. This is the
statement every consumer of the Fiedler vector starts from. -/
theorem fiedlerVector_eigen (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) :
    (laplacian A).mulVec (fiedlerVector A hA hcard)
      = lambda2 A hA hcard • fiedlerVector A hA hcard := by
  have hev := (isHermitian_of_isSymm (laplacian_symmetric A hA)
    ).mulVec_eigenvectorBasis (fiedlerIndex A hA hcard)
  rw [← fiedlerIndex_eigvalOf A hA hcard]
  exact hev

/-- The Fiedler vector has unit norm (it is a member of the orthonormal
eigenbasis), in dot-product form. -/
theorem fiedlerVector_norm (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) :
    Matrix.dotProduct (fiedlerVector A hA hcard) (fiedlerVector A hA hcard)
      = 1 := by
  have h := eigvecOf_inner (laplacian A) (laplacian_symmetric A hA)
    (fiedlerIndex A hA hcard) (fiedlerIndex A hA hcard)
  simpa using h

/-- The Fiedler vector is nonzero, by unit norm. -/
theorem fiedlerVector_ne_zero (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) :
    fiedlerVector A hA hcard ≠ 0 := by
  intro h
  have hn := fiedlerVector_norm A hA hcard
  rw [h, Matrix.dotProduct_zero] at hn
  exact zero_ne_one hn

/-- A unit eigenvector's quadratic form is its eigenvalue: the Fiedler
vector's Dirichlet energy is exactly `lambda2` — the value the
variational theory says is minimal among vectors orthogonal to the
constants. -/
theorem fiedlerVector_quadForm (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) :
    quadForm (laplacian A) (fiedlerVector A hA hcard)
      = lambda2 A hA hcard := by
  have h := quadForm_eigvecOf_self (laplacian_symmetric A hA)
    (fiedlerIndex A hA hcard)
  rw [fiedlerIndex_eigvalOf A hA hcard] at h
  exact h

/-- Eigenvectors at nonzero eigenvalues are orthogonal to `onesVec`;
for the Fiedler vector this needs `0 < lambda2`, which connectivity
supplies (`lambda2_pos_of_connected`). This orthogonality is the hinge
of the partition sanity facts below. -/
theorem fiedlerVector_ortho_onesVec (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) (hpos : 0 < lambda2 A hA hcard) :
    Matrix.dotProduct (fiedlerVector A hA hcard) onesVec = 0 := by
  refine eigvecOf_ortho_onesVec A hA ?_
  rw [fiedlerIndex_eigvalOf A hA hcard]
  exact hpos.ne'

/-- Orthogonality to the constants as a sum identity: the Fiedler
vector's entries sum to zero. This is the form the partition arguments
consume. -/
theorem fiedlerVector_sum_eq_zero (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) (hpos : 0 < lambda2 A hA hcard) :
    ∑ i, fiedlerVector A hA hcard i = 0 := by
  have h := fiedlerVector_ortho_onesVec A hA hcard hpos
  simpa [Matrix.dotProduct, onesVec] using h

/-!
## Algebraic connectivity: `lambda2 > 0` on connected graphs
-/

/-- **Fiedler's algebraic-connectivity certificate.** For a connected
graph with symmetric nonnegative weights, `0 < lambda2`.

Route (recorded before proving): PSD bounds every eigenbasis eigenvalue
below by zero (`quadForm_eigvecOf_self` + `laplacian_psd`), so a
nonpositive `lambda2` forces the first two sorted entries to coincide
at `0`; the lower multiplicity pin
(`exists_ne_eigvalOf_of_evals_head_eq`) then yields two *distinct*
eigenbasis vectors in the kernel; but on a connected graph the kernel is
exactly the line spanned by `onesVec`
(`laplacian_kernel_eq_span_onesVec`, the electrical program's step 2),
and two orthogonal unit vectors cannot share a line. This is a genuine
load-bearing consumer of the kernel characterization and of both
multiplicity pins — an error in any of them breaks this proof. -/
theorem lambda2_pos_of_connected (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) :
    0 < lambda2 A hA hcard := by
  by_contra hcon
  push_neg at hcon
  -- Every eigenbasis eigenvalue is nonnegative (PSD at unit vectors).
  have hge : ∀ i : V, 0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) i := by
    intro i
    rw [← quadForm_eigvecOf_self (laplacian_symmetric A hA) i]
    exact laplacian_psd A hA hnonneg _
  -- So both first sorted entries are pinned to 0: they are eigenbasis
  -- eigenvalues (≥ 0), sorted (≤ each other), and the second is ≤ 0.
  have hev0 : (0 : ℝ) ≤ evals (laplacian_symmetric A hA) ⟨0, by omega⟩ := by
    obtain ⟨i, hi⟩ :=
      evals_mem_eigvalOf (laplacian_symmetric A hA) ⟨0, by omega⟩
    rw [hi]; exact hge i
  have hmono : evals (laplacian_symmetric A hA) ⟨0, by omega⟩
      ≤ evals (laplacian_symmetric A hA) ⟨1, by omega⟩ :=
    evals_sorted (laplacian_symmetric A hA)
      (show (⟨0, by omega⟩ : Fin (Fintype.card V)) ≤ ⟨1, by omega⟩ by simp)
  have h1 : evals (laplacian_symmetric A hA) ⟨1, by omega⟩ = (0 : ℝ) :=
    le_antisymm hcon (hev0.trans hmono)
  have h0 : evals (laplacian_symmetric A hA) ⟨0, by omega⟩ = (0 : ℝ) :=
    le_antisymm (hmono.trans hcon) hev0
  -- Two distinct eigenbasis indices carry the common value 0.
  obtain ⟨i₁, i₂, hne, he1, he2⟩ := exists_ne_eigvalOf_of_evals_head_eq
    (laplacian_symmetric A hA) hcard (by rw [h0, h1])
  -- Their eigenvectors lie in the kernel, hence (connectivity) in the
  -- line spanned by `onesVec`.
  have hspan : ∀ i : V, eigvalOf (laplacian A) (laplacian_symmetric A hA) i = 0 →
      ∃ c : ℝ, c • onesVec = eigvecOf (laplacian A) (laplacian_symmetric A hA) i := by
    intro i hi
    have hmem : eigvecOf (laplacian A) (laplacian_symmetric A hA) i ∈
        Submodule.span ℝ ({onesVec} : Set (V → ℝ)) := by
      rw [← laplacian_kernel_eq_span_onesVec A hA hnonneg hconn,
        LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hev : (laplacian A).mulVec
          (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) = 0 := by
        have h := (isHermitian_of_isSymm (laplacian_symmetric A hA)
          ).mulVec_eigenvectorBasis i
        rw [show (isHermitian_of_isSymm (laplacian_symmetric A hA)).eigenvalues i
            = eigvalOf (laplacian A) (laplacian_symmetric A hA) i from rfl,
          hi, zero_smul] at h
        exact h
      exact hev
    exact Submodule.mem_span_singleton.1 hmem
  obtain ⟨c₁, hc₁⟩ := hspan i₁ (he1.trans h1)
  obtain ⟨c₂, hc₂⟩ := hspan i₂ (he2.trans h1)
  -- Orthonormality of the distinct pair, transported to the line.
  have hortho : Matrix.dotProduct
      (eigvecOf (laplacian A) (laplacian_symmetric A hA) i₁)
      (eigvecOf (laplacian A) (laplacian_symmetric A hA) i₂) = 0 := by
    have h := eigvecOf_inner (laplacian A) (laplacian_symmetric A hA) i₁ i₂
    simp only [if_neg hne] at h
    exact h
  have hn1 : Matrix.dotProduct
      (eigvecOf (laplacian A) (laplacian_symmetric A hA) i₁)
      (eigvecOf (laplacian A) (laplacian_symmetric A hA) i₁) = 1 := by
    have h := eigvecOf_inner (laplacian A) (laplacian_symmetric A hA) i₁ i₁
    simpa using h
  have hn2 : Matrix.dotProduct
      (eigvecOf (laplacian A) (laplacian_symmetric A hA) i₂)
      (eigvecOf (laplacian A) (laplacian_symmetric A hA) i₂) = 1 := by
    have h := eigvecOf_inner (laplacian A) (laplacian_symmetric A hA) i₂ i₂
    simpa using h
  rw [← hc₁, ← hc₂, dotProduct_smul_onesVec] at hortho
  rw [← hc₁, dotProduct_smul_onesVec] at hn1
  rw [← hc₂, dotProduct_smul_onesVec] at hn2
  have hcardpos : (0 : ℝ) < Fintype.card V := by
    have h : (0 : ℕ) < Fintype.card V := by omega
    exact_mod_cast h
  have hc1 : c₁ ≠ 0 := by
    intro h
    rw [h] at hn1
    simp at hn1
  have hc2 : c₂ ≠ 0 := by
    intro h
    rw [h] at hn2
    simp at hn2
  rcases mul_eq_zero.1 hortho with h | h
  · exact absurd h hcardpos.ne'
  · rcases mul_eq_zero.1 h with h | h
    · exact hc1 h
    · exact hc2 h

/-!
## A2: the induced sign partition
-/

/-- The Fiedler (sign-pattern) partition: the vertices where the Fiedler
vector is nonnegative. Noncomputable through the Fiedler vector; the
comparison uses a classical decidability instance on `ℝ`. On a
connected graph this is a genuine bipartition — nonempty
(`fiedlerPartition_nonempty`) and proper (`fiedlerPartition_ne_univ`). -/
noncomputable def fiedlerPartition (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) : Finset V :=
  Finset.univ.filter (fun i => 0 ≤ fiedlerVector A hA hcard i)

/-- Membership interface for the partition. -/
theorem fiedlerPartition_mem {A : WAdj (V := V)} {hA : A.IsSymm}
    {hcard : 2 ≤ Fintype.card V} {i : V} :
    i ∈ fiedlerPartition A hA hcard ↔ 0 ≤ fiedlerVector A hA hcard i :=
  Finset.mem_filter.trans (by simp)

/-- **A2 sanity, interface form:** the Fiedler partition is nonempty
whenever `0 < lambda2`. A vector whose entries sum to zero cannot be
everywhere strictly negative. The hypothesis is load-bearing: at
`lambda2 = 0` the Fiedler vector may be a kernel vector whose entries
are all nonnegative (see `Fiedler_QA`). -/
theorem fiedlerPartition_nonempty_of_pos (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) (hpos : 0 < lambda2 A hA hcard) :
    (fiedlerPartition A hA hcard).Nonempty := by
  by_contra hempty
  have hf : ∀ i : V, fiedlerVector A hA hcard i < 0 := by
    intro i
    by_contra hc
    push_neg at hc
    exact hempty ⟨i, fiedlerPartition_mem.2 hc⟩
  apply fiedlerVector_ne_zero A hA hcard
  have hsum := fiedlerVector_sum_eq_zero A hA hcard hpos
  have hsumneg : ∑ j ∈ Finset.univ, -fiedlerVector A hA hcard j = 0 := by
    rw [Finset.sum_neg_distrib, hsum, neg_zero]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => neg_nonneg.2 (hf j).le)).1 hsumneg
  funext i
  simp only [Pi.zero_apply]
  have := hzero i (Finset.mem_univ i)
  linarith

/-- **A2 sanity, interface form:** the Fiedler partition is proper
(different from `univ`) whenever `0 < lambda2`. A nonzero vector whose
entries sum to zero cannot be everywhere nonnegative. The hypothesis is
load-bearing in the same way as above. -/
theorem fiedlerPartition_ne_univ_of_pos (A : WAdj (V := V)) (hA : A.IsSymm)
    (hcard : 2 ≤ Fintype.card V) (hpos : 0 < lambda2 A hA hcard) :
    fiedlerPartition A hA hcard ≠ Finset.univ := by
  intro heq
  apply fiedlerVector_ne_zero A hA hcard
  have hsum := fiedlerVector_sum_eq_zero A hA hcard hpos
  have hnn : ∀ j : V, (0 : ℝ) ≤ fiedlerVector A hA hcard j := by
    intro j
    have hj : j ∈ fiedlerPartition A hA hcard := by
      rw [heq]; exact Finset.mem_univ j
    exact fiedlerPartition_mem.1 hj
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => hnn j)).1 hsum
  funext i
  simp only [Pi.zero_apply]
  exact hzero i (Finset.mem_univ i)

/-- **A2 sanity:** on a connected graph with symmetric nonnegative
weights, the Fiedler partition is nonempty. -/
theorem fiedlerPartition_nonempty (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) :
    (fiedlerPartition A hA hcard).Nonempty :=
  fiedlerPartition_nonempty_of_pos A hA hcard
    (lambda2_pos_of_connected A hA hnonneg hcard hconn)

/-- **A2 sanity:** on a connected graph with symmetric nonnegative
weights, the Fiedler partition is proper — a genuine bipartition. -/
theorem fiedlerPartition_ne_univ (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) :
    fiedlerPartition A hA hcard ≠ Finset.univ :=
  fiedlerPartition_ne_univ_of_pos A hA hcard
    (lambda2_pos_of_connected A hA hnonneg hcard hconn)

/-!
## Phase B: the certified conductance cut

`proposals/fiedler-partitioning.md` Phase B, delivered 2026-08-23 as
pure hard crust (zero new axioms): the hard direction of Cheeger was
proved the same day
(`GraphTheory.Cheeger.cheeger_lower_bound`/`cheeger_sweep`), dissolving
the proposal's recorded gate. The certificate is the classical Cheeger
cut-existence corollary rather than the sketch's sign-partition bound —
see the module header for the recorded statement-shape deviation.
-/

/-- The Fiedler vector's Rayleigh quotient at the regular normalized
Laplacian is `lambda2 / d`: unit norm, the quadratic-form transfer
`quadForm (L_sym) = d⁻¹ • quadForm (laplacian)`, and the energy
identity `quadForm (laplacian) f = lambda2`. This is the bridge through
which the proved sweep lemma's spectral side (`rayleigh` of the
normalized operator) reads the combinatorial eigenvalue that
`lambda2_pos_of_connected` certifies.

QA: `SpectralGraphTheory.QA.k2_fiedler_rayleigh_QA` in
`Scaffold/QA/SpectralGraph/Fiedler_QA.lean` pins the value on `K₂` to
`2` and cross-checks it against the independently pinned
`λ₂(L_sym) = 2`. -/
theorem fiedlerVector_rayleigh_regularNormalizedLaplacian
    (A : WAdj (V := V)) (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V)
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d) :
    rayleigh (regularNormalizedLaplacian A d) (fiedlerVector A hA hcard)
      = lambda2 A hA hcard / d := by
  rw [rayleigh, if_neg (fiedlerVector_ne_zero A hA hcard),
    quadForm_regularNormalizedLaplacian A d hd hdpos.ne',
    fiedlerVector_quadForm A hA hcard, fiedlerVector_norm A hA hcard,
    div_one]
  exact inv_mul_eq_div d _

/-- **Phase B: the certified conductance cut.** On every connected
`d`-regular graph with symmetric nonnegative weights there exists a
nonempty proper vertex set whose conductance satisfies
`φ(S) ^ 2 ≤ 2 λ₂(L) / d` — the classical cut-existence corollary of
Cheeger's inequality (`φ(G) ^ 2 / 2 ≤ λ₂(L_sym)` with
`λ₂(L_sym) = λ₂(L) / d`), made *existential* by the attained conductance
minimum (`cheegerConstant_attained`).

Trust level: hard crust. Every ingredient is proved — the sweep lemma
(`cheeger_sweep`, proved 2026-08-23), attainment (finiteness), the
Rayleigh transfer above, and the algebraic-connectivity certificate
(`lambda2_pos_of_connected`, Phase A). Nothing axiom-backed enters.

Statement difference from the proposal's Phase B sketch, recorded
before stating: the sketch bounded the conductance of the *sign*
partition `fiedlerPartition`; the Cheeger inequalities cannot certify
any specific cut's conductance from `lambda2` alone — they bound the
minimum — and the sign half-space admits no λ₂-only bound in general.
The certified object here is therefore the conductance-minimizing cut
(whose *value* is bounded, through the Fiedler vector's Rayleigh
quotient), and certifying an explicitly swept Fiedler level set is the
recorded follow-on.

QA: `SpectralGraphTheory.QA.k2_cut_certified_QA`,
`SpectralGraphTheory.QA.k2_cut_identified_QA`, and
`SpectralGraphTheory.QA.cut_existence_regular_dropped_refuted_QA` in
`Scaffold/QA/SpectralGraph/Fiedler_QA.lean`. -/
theorem cheeger_cut_existence (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance A S ^ 2 ≤ 2 * lambda2 A hA hcard / d := by
  obtain ⟨S, hS, hSc, hSφ⟩ := cheegerConstant_attained A hnn hcard
  refine ⟨S, hS, hSc, ?_⟩
  have hsweep := cheeger_sweep A hA hnn d hd hdpos
    (fiedlerVector_ne_zero A hA hcard)
    (fiedlerVector_ortho_onesVec A hA hcard
      (lambda2_pos_of_connected A hA hnn hcard hconn))
  rw [fiedlerVector_rayleigh_regularNormalizedLaplacian A hA hcard d
    hd hdpos] at hsweep
  rw [hSφ, le_div_iff₀ hdpos]
  have h2 := (div_le_iff₀ two_pos).1 hsweep
  calc cheegerConstant A ^ 2 * d
      ≤ (lambda2 A hA hcard / d * 2) * d :=
        mul_le_mul_of_nonneg_right h2 hdpos.le
    _ = 2 * lambda2 A hA hcard := by
        rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hdpos.ne']; ring

end SpectralGraphTheory
