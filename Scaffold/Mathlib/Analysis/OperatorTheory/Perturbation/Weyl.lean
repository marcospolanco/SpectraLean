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
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Weyl perturbation bounds

Weyl's inequality bounds the movement of each eigenvalue of a real
symmetric matrix under a symmetric perturbation, in the ℓ² operator
norm. Eigenvalues are indexed through Scaffold's sorted spectrum
`SpectralGraphTheory.evals`; the norm is the `Matrix.L2OpNorm` operator
norm on `Matrix V V ℝ`.

**No statement is admitted in this module anymore.** The one classical
result that remained an `axiom` here — `weyl_inequality` — was retired
on 2026-08-20 (`proposals/discharge-perturbation-axioms.md`, Weyl target
only) and is proved below at its unchanged name, hypotheses, and
conclusion, from two ingredients delivered earlier as hard crust:

- the *additive* Weyl bounds (`weyl_additive_upper`,
  `weyl_additive_lower`), proved from the general Courant–Fischer
  min–max engine (`evals_min_max` and its two witness forms) exactly as
  the Cauchy-interlacing retirement was; and
- the operator-norm bridge `l2OpNorm_eq_max_abs_evals`
  (`Analysis.OperatorTheory.Resolvent`), which turns the additive
  window `[λᵢ(A) + λ₁(E), λᵢ(A) + λₙ(E)]` into the spectral-norm
  statement `|λᵢ(A + E) − λᵢ(A)| ≤ ‖E‖`.

The step-0 spike recorded in the proposal confirmed the additive bound
is not a free corollary of the norm bridge (it needs both Courant–Fischer
witness directions plus both Rayleigh domination bounds), but is cheap
alongside them.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Translation bookkeeping

The Courant–Fischer engine speaks in Rayleigh quotients; the domination
bounds speak in multiplication form. These two private restatements
move between the two, and quadratic-form additivity is restated locally
(the generic `SpectralGraphTheory.quadForm_add` lives in
`GraphTheory.Expander`, an outer consumer this perturbation module must
not depend on).
-/

omit [DecidableEq V] in
/-- Multiplication-form restatement of a Rayleigh upper bound:
`R(x) ≤ r ↔ xᵀMx ≤ r • (x ⬝ᵥ x)` for `x ≠ 0`. -/
private theorem rayleigh_le_iff_mul {M : Matrix V V ℝ} {x : V → ℝ}
    (hx0 : x ≠ 0) {r : ℝ} :
    rayleigh M x ≤ r ↔ quadForm M x ≤ r * Matrix.dotProduct x x := by
  have hDpos : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
  rw [rayleigh, if_neg hx0, div_le_iff₀ hDpos]

omit [DecidableEq V] in
/-- Multiplication-form restatement of a Rayleigh lower bound:
`r ≤ R(x) ↔ r • (x ⬝ᵥ x) ≤ xᵀMx` for `x ≠ 0`. -/
private theorem le_rayleigh_iff_mul {M : Matrix V V ℝ} {x : V → ℝ}
    (hx0 : x ≠ 0) {r : ℝ} :
    r ≤ rayleigh M x ↔ r * Matrix.dotProduct x x ≤ quadForm M x := by
  have hDpos : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
  rw [rayleigh, if_neg hx0, le_div_iff₀ hDpos]

omit [DecidableEq V] in
/-- Quadratic forms are additive in the matrix (local copy of
`SpectralGraphTheory.quadForm_add`; kept private to avoid a dependency
on the `GraphTheory.Expander` module). -/
private theorem quadForm_add' (M N : Matrix V V ℝ) (x : V → ℝ) :
    quadForm (M + N) x = quadForm M x + quadForm N x := by
  show x ⬝ᵥ ((M + N) *ᵥ x) = x ⬝ᵥ (M *ᵥ x) + x ⬝ᵥ (N *ᵥ x)
  rw [Matrix.add_mulVec, Matrix.dotProduct_add]

/-!
## The additive Weyl bounds (proved)

`λᵢ(A) + λ₁(E) ≤ λᵢ(A + E) ≤ λᵢ(A) + λₙ(E)` at every sorted index.
Both directions are Courant–Fischer consequences, in the same shape as
the delivered Cauchy-interlacing proof: the upper bound exhibits the
existence-direction witness subspace for `A` as a competitor for the
infimum defining `λᵢ(A + E)` (on it, Rayleigh quotients of `A + E`
split as `R_A + R_E`, with `R_A ≤ λᵢ(A)` by the witness and `R_E ≤
λₙ(E)` by top Rayleigh domination everywhere); the lower bound runs the
competitor direction for `A` inside the witness subspace for `A + E`
(every vector there has `R_{A+E} ≤ λᵢ(A+E)`, so the competitor's
`λᵢ(A) ≤ R_A = R_{A+E} − R_E` leaves `λᵢ(A) + λ₁(E) ≤ λᵢ(A+E)` once
`R_E ≥ λ₁(E)` by bottom Rayleigh domination).
-/

/-- **Additive Weyl bound, upper:** `λᵢ(A + E) ≤ λᵢ(A) + λₙ(E)` for
symmetric `A, E` at every sorted index — the top half of the additive
window. Load-bearing on the Courant–Fischer engine: the witness
subspace `W₀` from `exists_submodule_forall_rayleigh_le` at index `i`
for `A` is exhibited as a member of the competitor set defining
`λᵢ(A + E)` through `evals_min_max`.

Source (classical background; this is a proof, not an admission):
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.3, Theorem 4.3.1 (Weyl).
- Bhatia, R., "Matrix Analysis", Springer, 1997, Section III.2.

Statement differences: eigenvalues are the sorted `evals` of
`SpectralGraphTheory`; the cardinality hypothesis keeps the last index
inhabited (the full statement `weyl_inequality` is vacuous below one
vertex).

QA: `weyl_additive_upper_QA` in `Scaffold/QA/Perturbation/Weyl_QA.lean`
instantiates the bound on a two-vertex fixture with all three spectra
pinned from trace/determinant/sortedness.
-/
theorem weyl_additive_upper (A E : Matrix V V ℝ) (hA : A.IsSymm)
    (hE : E.IsSymm) (hcard : 1 ≤ Fintype.card V)
    (i : Fin (Fintype.card V)) :
    evals (hA.add hE) i
      ≤ evals hA i + evals hE ⟨Fintype.card V - 1, by omega⟩ := by
  obtain ⟨W₀, hW₀r, hW₀b⟩ := exists_submodule_forall_rayleigh_le hA i
  have hbound : ∀ x ∈ W₀, x ≠ 0 → rayleigh (A + E) x
      ≤ evals hA i + evals hE ⟨Fintype.card V - 1, by omega⟩ := by
    intro x hx hx0
    have hDbound : quadForm A x ≤ evals hA i * Matrix.dotProduct x x :=
      (rayleigh_le_iff_mul hx0).1 (hW₀b x hx hx0)
    have hEbound : quadForm E x
        ≤ evals hE ⟨Fintype.card V - 1, by omega⟩ * Matrix.dotProduct x x :=
      quadForm_le_evals_last hE hcard x
    refine (rayleigh_le_iff_mul hx0).2 ?_
    rw [quadForm_add' A E x]
    have hring : (evals hA i
        + evals hE ⟨Fintype.card V - 1, by omega⟩) * Matrix.dotProduct x x
        = evals hA i * Matrix.dotProduct x x
          + evals hE ⟨Fintype.card V - 1, by omega⟩ * Matrix.dotProduct x x := by
      ring
    linarith
  have hbdd : BddBelow {r : ℝ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = (i : ℕ) + 1 ∧
      ∀ x ∈ W, x ≠ 0 → rayleigh (A + E) x ≤ r} :=
    ⟨evals (hA.add hE) i, by
      rintro r ⟨W, hWr, hWb⟩
      obtain ⟨x, hxW, hx0, hxge⟩ :=
        exists_ne_mem_rayleigh_ge_of_finrank_eq (hA.add hE) i W hWr
      exact hxge.trans (hWb x hxW hx0)⟩
  rw [evals_min_max (hA.add hE) i]
  exact csInf_le hbdd ⟨W₀, hW₀r, hbound⟩

/-- **Additive Weyl bound, lower:** `λᵢ(A) + λ₁(E) ≤ λᵢ(A + E)` for
symmetric `A, E` at every sorted index — the bottom half of the additive
window. Load-bearing on the Courant–Fischer engine in the competitor
direction: the witness subspace for `A + E` at index `i` has dimension
`i + 1`, so it contains a nonzero vector whose `A`-Rayleigh quotient is
at least `λᵢ(A)`; on that subspace `R_A = R_{A+E} − R_E ≤ λᵢ(A+E) −
λ₁(E)` by the witness bound plus bottom Rayleigh domination.

Source (classical background; this is a proof, not an admission):
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.3, Theorem 4.3.1 (Weyl).
- Bhatia, R., "Matrix Analysis", Springer, 1997, Section III.2.

Statement differences: as in `weyl_additive_upper`.

QA: `weyl_additive_lower_QA` in `Scaffold/QA/Perturbation/Weyl_QA.lean`.
-/
theorem weyl_additive_lower (A E : Matrix V V ℝ) (hA : A.IsSymm)
    (hE : E.IsSymm) (hcard : 1 ≤ Fintype.card V)
    (i : Fin (Fintype.card V)) :
    evals hA i + evals hE ⟨0, by omega⟩ ≤ evals (hA.add hE) i := by
  obtain ⟨W₁, hW₁r, hW₁b⟩ := exists_submodule_forall_rayleigh_le (hA.add hE) i
  obtain ⟨x, hxW, hx0, hxge⟩ :=
    exists_ne_mem_rayleigh_ge_of_finrank_eq hA i W₁ hW₁r
  have hDpos : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
  have hxge' : evals hA i * Matrix.dotProduct x x ≤ quadForm A x :=
    (le_rayleigh_iff_mul hx0).1 hxge
  have hEbound : evals hE ⟨0, by omega⟩ * Matrix.dotProduct x x
      ≤ quadForm E x := evals_first_mul_dotProduct_le_quadForm hE hcard x
  have hAEb : quadForm (A + E) x
      ≤ evals (hA.add hE) i * Matrix.dotProduct x x :=
    (rayleigh_le_iff_mul hx0).1 (hW₁b x hxW hx0)
  rw [quadForm_add' A E x] at hAEb
  have hring : (evals hA i + evals hE ⟨0, by omega⟩) * Matrix.dotProduct x x
      = evals hA i * Matrix.dotProduct x x
        + evals hE ⟨0, by omega⟩ * Matrix.dotProduct x x := by ring
  have hmul : (evals hA i + evals hE ⟨0, by omega⟩) * Matrix.dotProduct x x
      ≤ evals (hA.add hE) i * Matrix.dotProduct x x := by
    linarith
  exact (mul_le_mul_iff_of_pos_right hDpos).1 hmul

/-- Weyl's inequality: every eigenvalue of a symmetric matrix moves by at
most the operator norm of a symmetric perturbation. With the spectra of
`A` and `A + E` sorted in nondecreasing order, `|λᵢ(A + E) - λᵢ(A)| ≤ ‖E‖`
for every index `i`.

Retired from an admitted axiom to a proved theorem on 2026-08-20
(`proposals/discharge-perturbation-axioms.md`), at the unchanged name,
hypotheses, and conclusion — the `sherman_morrison` /
`woodbury_identity` / `eigen_interlacing` retirement precedent. Route:
the additive window `λᵢ(A) + λ₁(E) ≤ λᵢ(A+E) ≤ λᵢ(A) + λₙ(E)`
(`weyl_additive_lower`/`weyl_additive_upper` above) composed with the
proved operator-norm bridge `l2OpNorm_eq_max_abs_evals`
(`Analysis.OperatorTheory.Resolvent`): both window endpoints sit within
`±‖E‖` of `λᵢ(A)` because `‖E‖ = max |λ₁(E)| |λₙ(E)|`. The cardinality
hypothesis of the bridge is no restriction here: below one vertex there
is no index to quantify over, so the statement is vacuous.

Source (classical background; this is a proof, not an admission):
- Weyl, H., "Das asymptotische Verteilungsgesetz der Eigenwerte linearer
  partieller Differentialgleichungen", Mathematische Annalen 71(4):441–479,
  1912.
- Bhatia, R., "Matrix Analysis", Springer, 1997, Theorem III.2.1.

Statement differences: eigenvalues are the sorted `evals` of
`SpectralGraphTheory` and the norm is the ℓ² operator norm, matching the
matrix-first representation convention of the SGT center. The cited
theorem is the general additive Weyl inequality; the Lean statement is
its spectral-norm corollary for a symmetric perturbation, obtained by
combining the (now proved) additive bound with `λ₁(E) ≤ ‖E‖` and
`λₙ(E) ≥ -‖E‖` through `l2OpNorm_eq_max_abs_evals`.

QA: exercised by `zero_perturbation_QA` and
`weyl_nonzero_perturbation_QA` in
`Scaffold/QA/Perturbation/Weyl_QA.lean` (zero perturbation: the identity
bound; nonzero perturbation on a fixture with all spectra pinned: the
bound attained at one index and strict at the other).
-/
theorem weyl_inequality (A E : Matrix V V ℝ) (hA : A.IsSymm) (hE : E.IsSymm)
    (i : Fin (Fintype.card V)) :
    |evals (hA.add hE) i - evals hA i| ≤ ‖E‖ := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · exact absurd i.isLt (by omega)
  have hcard : 1 ≤ Fintype.card V := hpos
  have hu := weyl_additive_upper A E hA hE hcard i
  have hl := weyl_additive_lower A E hA hE hcard i
  rw [Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_eq_max_abs_evals
    hE hcard]
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [neg_le_abs (evals hE ⟨0, by omega⟩),
      le_max_left |evals hE ⟨0, by omega⟩|
        |evals hE ⟨Fintype.card V - 1, by omega⟩|]
  · linarith [le_abs_self (evals hE ⟨Fintype.card V - 1, by omega⟩),
      le_max_right |evals hE ⟨0, by omega⟩|
        |evals hE ⟨Fintype.card V - 1, by omega⟩|]

/-- Stability of a spectral gap under Weyl perturbation: if `E` moves the
matrix by at most `ε` in operator norm, the gap at index `k` shrinks by
at most `2ε` (each endpoint of the gap moves by at most `ε`).

Dependency status: proved. Formerly "proved from the admitted
`weyl_inequality`"; since that retirement (2026-08-20) the whole chain
here is hard crust — `weyl_inequality` at both gap endpoints plus
arithmetic.

Source:
- Corollary of `weyl_inequality` as stated above; see Bhatia, "Matrix
  Analysis", Springer, 1997, Chapter III.2.

QA: exercised by `spectral_gap_zero_perturbation_QA` in
`Scaffold/QA/Perturbation/Weyl_QA.lean` (zero-perturbation instance).
-/
theorem spectral_gap_stability (A E : Matrix V V ℝ) (hA : A.IsSymm)
    (hE : E.IsSymm) (k : Fin (Fintype.card V))
    (hk : (k : ℕ) + 1 < Fintype.card V) (ε : ℝ) (hnorm : ‖E‖ ≤ ε)
    (γ : ℝ) (hγ : spectralGap A hA k hk ≥ γ) :
    spectralGap (A + E) (hA.add hE) k hk ≥ γ - 2 * ε := by
  have hw1 := abs_le.mp (weyl_inequality A E hA hE ⟨(k : ℕ) + 1, hk⟩)
  have hw2 := abs_le.mp (weyl_inequality A E hA hE ⟨(k : ℕ), k.isLt⟩)
  have hgapA : spectralGap A hA k hk
      = evals hA ⟨(k : ℕ) + 1, hk⟩ - evals hA ⟨(k : ℕ), k.isLt⟩ := rfl
  have hgapAE : spectralGap (A + E) (hA.add hE) k hk
      = evals (hA.add hE) ⟨(k : ℕ) + 1, hk⟩
        - evals (hA.add hE) ⟨(k : ℕ), k.isLt⟩ := rfl
  rw [hgapA] at hγ
  rw [hgapAE]
  linarith

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
