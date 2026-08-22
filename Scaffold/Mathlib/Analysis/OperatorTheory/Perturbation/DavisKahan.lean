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
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Duhamel
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Davis–Kahan subspace stability

The Davis–Kahan sin Θ theorem bounds the rotation of an invariant
spectral subspace of a symmetric matrix under symmetric perturbation,
inversely to the eigenvalue separation. Stated here for the spectral
projectors of the SGT center, with the ℓ² operator norm.

**Retired from axiom to proved theorem on 2026-08-21** (explicit axioms
11 → 10), at the unchanged name, hypotheses, and conclusion, along the
route surveyed in `proposals/discharge-perturbation-axioms.md` (Step 0,
2026-08-21) and delivered by its two components: the equal-rank
projector identity
(`ProjectionGap.l2OpNorm_sub_eq_of_rank_eq`, component 1) and the
Duhamel/exponential-integral bound
(`Duhamel.l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le`,
component 2). `#print axioms` reads only `propext, Classical.choice,
Quot.sound`.

The proof is a three-way case split on eigenvalue ties at the two
thresholds (a tie-awareness the survey did not need to resolve, recorded
here at delivery):

- **No tie at either `k`-th threshold:** both `initialProjector`s have
  rank exactly `k + 1` (`Duhamel.rank_spectralProjector_evals_of_lt`), so
  the equal-rank identity converts the goal to `‖(I − Q) * P‖`, which
  the Duhamel bound caps at `‖E‖ / (λ_{k+1}(A+E) − λ_k(A)) ≤ ‖E‖/δ`.
- **Tie at `(A + E)`'s threshold** (`λ_k(A+E) = λ_{k+1}(A+E)`): the
  separation hypothesis plus the proved Weyl additive upper bound at
  index `k` force `δ ≤ ‖E‖`, and the unconditional projector-distance
  bound `‖P − Q‖ ≤ 1` finishes `‖P − Q‖ ≤ 1 ≤ ‖E‖/δ`.
- **Tie at `A`'s threshold** (`λ_k(A) = λ_{k+1}(A)`): same conclusion
  through Weyl at index `k + 1`.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Davis–Kahan sin Θ bound for spectral projectors: if the top of the
lower cluster of `A` (its `k`-th sorted eigenvalue) is separated by at
least `δ` from the bottom of the upper cluster of `A + E` (its `k+1`-st
sorted eigenvalue), then the projector onto the span of the `k+1`
smallest eigenvectors moves by at most `‖E‖ / δ`.

Proved (2026-08-21) by the Duhamel/exponential-integral route; see the
module documentation. The statement below is byte-for-byte the axiom it
replaces.

Source (statement provenance; the proof above is self-contained):
- Davis, C. & Kahan, W. M., "The rotation of eigenvectors by a
  perturbation", SIAM Journal on Numerical Analysis 7(1):1–46, 1970.
- Yu, Y., Wang, T., Samworth, R. J., "A useful variant of the Davis–Kahan
  theorem for statisticians", Annals of Statistics 43(3):2028–2061, 2015,
  Theorem 1 — the classical Davis–Kahan sin Θ bound restated with the
  mixed population/sample separation `δ = inf{|λ̂ − λ| : λ in the
  population cluster, λ̂ in the sample outside-cluster set|}` and constant
  1; the paper notes both Frobenius norms there may be replaced by the
  operator norm. This statement is that operator-norm form specialized
  to the bottom cluster (the `k+1` smallest eigenvalues, `d = k+1`).

Citation correction 2026-08-21 (Step-0 survey of
`proposals/discharge-perturbation-axioms.md`, paper read at
arXiv:1405.0680): an earlier revision of this note cited "Theorem 2
(two-sided separation, projector form, constant 1)" — a locator/constant
pairing that does not exist in the paper. YWS's actual Theorem 2 is a
*population-gap* result with constant 2 (numerator
`2 min(d^{1/2}‖E‖_op, ‖E‖_F)`, Frobenius norm, proved via Weyl and
Wielandt–Hoffman); this statement's mixed-gap operator-norm constant-1
shape is their Theorem 1.

Statement differences: the invariant subspaces are the
`SpectralGraphTheory.initialProjector` spectral projectors of the sorted
spectrum; the distance is the ℓ² operator norm of the projector
difference (the sin Θ metric). The separation hypothesis is the
two-cluster gap `λ_{k+1}(A + E) - λ_k(A) ≥ δ`, the single-pair reduction
(by sortedness; `SpectralGraphTheory.evals_sorted`) of YWS Theorem 1's
`δ` for the bottom cluster — there the outside-cluster set is only the
upper one, so the binding pair is the top of `A`'s cluster against the
bottom of `A + E`'s complement. An earlier revision of this axiom
quantified pairwise; it was tightened to the single-pair form on
2026-08-17 during citation review.

QA: exercised by the zero-perturbation and strict-rotation instances in
`Scaffold/QA/Perturbation/DavisKahan_QA.lean`.
-/
theorem davis_kahan_sin_theta
    (A E : Matrix V V ℝ) (hA : A.IsSymm) (hAE : (A + E).IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : δ ≤ evals hAE ⟨(k : ℕ) + 1, hk⟩ - evals hA ⟨(k : ℕ), k.isLt⟩) :
    ‖initialProjector (A + E) hAE k - initialProjector A hA k‖ ≤ ‖E‖ / δ := by
  classical
  have hcard : 1 ≤ Fintype.card V := by omega
  have hE : E.IsSymm := by
    have hsub := hAE.sub hA
    have hEq : (A + E) - A = E := by
      ext i j; simp
    rwa [hEq] at hsub
  have hbige : evals hE ⟨Fintype.card V - 1, by omega⟩ ≤ ‖E‖ := by
    rw [Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_eq_max_abs_evals
      hE hcard]
    exact le_trans (le_abs_self _) (le_max_right _ _)
  have hle1 : ‖initialProjector (A + E) hAE k - initialProjector A hA k‖ ≤ 1 :=
    l2OpNorm_sub_le_one_of_isSymm_idempotent
      (initialProjector_symmetric (A + E) hAE k)
      (initialProjector_idempotent (A + E) hAE k)
      (initialProjector_symmetric A hA k)
      (initialProjector_idempotent A hA k)
  rcases lt_or_ge (evals hA ⟨(k : ℕ), k.isLt⟩)
      (evals hA ⟨(k : ℕ) + 1, hk⟩) with hAT | hAT
  · rcases lt_or_ge (evals hAE ⟨(k : ℕ), k.isLt⟩)
      (evals hAE ⟨(k : ℕ) + 1, hk⟩) with hAET | hAET
    · -- no tie at either threshold: equal ranks, the Duhamel bound
      have hrP : (spectralProjector A hA (evals hA ⟨(k : ℕ), k.isLt⟩)).rank
          = (k : ℕ) + 1 := rank_spectralProjector_evals_of_lt hA k hk hAT
      have hrQ : (spectralProjector (A + E) hAE
          (evals hAE ⟨(k : ℕ), k.isLt⟩)).rank
          = (k : ℕ) + 1 := rank_spectralProjector_evals_of_lt hAE k hk hAET
      have hPsymm : (spectralProjector A hA (evals hA ⟨(k : ℕ), k.isLt⟩)).IsSymm :=
        spectralProjector_symmetric _ _ _
      have hPidem : spectralProjector A hA (evals hA ⟨(k : ℕ), k.isLt⟩)
          * spectralProjector A hA (evals hA ⟨(k : ℕ), k.isLt⟩)
          = spectralProjector A hA (evals hA ⟨(k : ℕ), k.isLt⟩) :=
        spectralProjector_idempotent _ _ _
      have hQsymm : (spectralProjector (A + E) hAE
          (evals hAE ⟨(k : ℕ), k.isLt⟩)).IsSymm :=
        spectralProjector_symmetric _ _ _
      have hQidem : spectralProjector (A + E) hAE (evals hAE ⟨(k : ℕ), k.isLt⟩)
          * spectralProjector (A + E) hAE (evals hAE ⟨(k : ℕ), k.isLt⟩)
          = spectralProjector (A + E) hAE (evals hAE ⟨(k : ℕ), k.isLt⟩) :=
        spectralProjector_idempotent _ _ _
      rw [show initialProjector (A + E) hAE k
          = spectralProjector (A + E) hAE (evals hAE ⟨(k : ℕ), k.isLt⟩) from rfl,
        show initialProjector A hA k
          = spectralProjector A hA (evals hA ⟨(k : ℕ), k.isLt⟩) from rfl,
        ← neg_sub, norm_neg,
        l2OpNorm_sub_eq_of_rank_eq hPsymm hPidem hQsymm hQidem
          (by rw [hrP, hrQ])]
      have hab : evals hA ⟨(k : ℕ), k.isLt⟩
          < evals hAE ⟨(k : ℕ) + 1, hk⟩ := by linarith
      calc ‖(1 - spectralProjector (A + E) hAE (evals hAE ⟨(k : ℕ), k.isLt⟩))
            * spectralProjector A hA (evals hA ⟨(k : ℕ), k.isLt⟩)‖
          ≤ ‖E‖ / (evals hAE ⟨(k : ℕ) + 1, hk⟩
              - evals hA ⟨(k : ℕ), k.isLt⟩) :=
            l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le
              hA hAE _ _ _ hab
              (fun i hi => evals_succ_le_of_lt hAE k hk hi)
        _ ≤ ‖E‖ / δ := by
            rw [div_le_div_iff₀ (by linarith) hδ]
            exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg E)
    · -- tie at the (A + E) threshold: Weyl at index k forces δ ≤ ‖E‖
      have hc'b : evals hAE ⟨(k : ℕ), k.isLt⟩
          = evals hAE ⟨(k : ℕ) + 1, hk⟩ :=
        le_antisymm (evals_sorted hAE (Fin.mk_le_mk.2 (by omega))) hAET
      have hw : evals hAE ⟨(k : ℕ), k.isLt⟩
          ≤ evals hA ⟨(k : ℕ), k.isLt⟩
            + evals hE ⟨Fintype.card V - 1, by omega⟩ :=
        weyl_additive_upper A E hA hE hcard ⟨(k : ℕ), k.isLt⟩
      have hEδ : δ ≤ ‖E‖ := by linarith
      have hone : 1 ≤ ‖E‖ / δ := (one_le_div hδ).2 hEδ
      linarith
  · -- tie at the A threshold: Weyl at index k+1 forces δ ≤ ‖E‖
    have hab' : evals hA ⟨(k : ℕ) + 1, hk⟩
        = evals hA ⟨(k : ℕ), k.isLt⟩ :=
      le_antisymm hAT (evals_sorted hA (Fin.mk_le_mk.2 (by omega)))
    have hw : evals hAE ⟨(k : ℕ) + 1, hk⟩
        ≤ evals hA ⟨(k : ℕ) + 1, hk⟩
          + evals hE ⟨Fintype.card V - 1, by omega⟩ :=
      weyl_additive_upper A E hA hE hcard ⟨(k : ℕ) + 1, hk⟩
    have hEδ : δ ≤ ‖E‖ := by linarith
    have hone : 1 ≤ ‖E‖ / δ := (one_le_div hδ).2 hEδ
    linarith

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
