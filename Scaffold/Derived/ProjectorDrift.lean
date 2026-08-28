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
import Scaffold.Derived.EventStream
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan

/-!
# High-probability projector drift (derived layer)

Second derived module: bounds high-probability spectral-projector drift
end-to-end. The random cumulative Laplacian displacement `‖L_m − L_0‖` is
controlled in probability by Azuma (`eventStreamTail`); the deterministic
response of the invariant spectral subspace to that displacement is
controlled by Weyl plus Davis–Kahan.

Everything here is either proved (`initialProjector_congr`,
`evals_sorted`, telescoping, measure monotonicity — and, since the
2026-08-20 retirement, `weyl_inequality`) or an explicit combination of
the admitted axioms `davis_kahan_sin_theta` and
`matrix_azuma_hoeffding`. No new axioms are introduced, and the
conclusions are conditional on the axioms they
consume; they are not foundationally proved results.

The composition is *two-endpoint* rather than per-step: Davis–Kahan is a
two-point statement at `(B, B + E)`, and the Azuma input controls exactly
the two-endpoint displacement `‖L_m − L_0‖`. A per-step bound is
available, at a cruder constant, by summing this two-endpoint bound over
consecutive times.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory.Derived

open Scaffold.Mathlib.Probability.Concentration.Matrix
open Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Two-point Davis–Kahan with a gap hypothesis (axiom-backed)
-/

/-- Davis–Kahan in two-point form with the separation discharged from a
spectral-gap hypothesis: if `B` has spectral gap at least
`‖C − B‖ + δ` at index `k`, then the `k`-th initial projector moves from
`B` to `C` by at most `‖C − B‖ / δ`.

Dependency status: derived from the admitted `davis_kahan_sin_theta`
(Davis–Kahan sin Θ, single-pair cluster separation) and `weyl_inequality`
(Weyl, at the gap index only — itself a proved theorem since the
2026-08-20 retirement, no longer an axiom dependency). Conditional on
that one axiom.

The gap hypothesis is honest: by Weyl at index `k + 1`, the bottom of the
upper cluster of `C = B + E` stays above the bottom of the upper cluster
of `B` minus `‖E‖`, so `λ_{k+1}(C) - λ_k(B) ≥ gap_B - ‖E‖ ≥ δ`.

QA: exercised by `davisKahanTwoPoint_self_QA` in
`Scaffold/QA/Derived/ProjectorDrift_QA.lean` (instantiation at `C = B`).
-/
theorem davisKahanTwoPoint (B C : Matrix V V ℝ) (hB : B.IsSymm)
    (hC : C.IsSymm) (k : Fin (Fintype.card V))
    (hk : (k : ℕ) + 1 < Fintype.card V) (δ : ℝ) (hδ : 0 < δ)
    (hδle : δ ≤ spectralGap B hB k hk - ‖C - B‖) :
    ‖initialProjector C hC k - initialProjector B hB k‖ ≤ ‖C - B‖ / δ := by
  have hE : (C - B).IsSymm := hC.sub hB
  have hw := abs_le.mp (weyl_inequality B (C - B) hB hE ⟨(k : ℕ) + 1, hk⟩)
  have hgapB : spectralGap B hB k hk
      = evals hB ⟨(k : ℕ) + 1, hk⟩ - evals hB ⟨(k : ℕ), k.isLt⟩ := rfl
  have hdk := davis_kahan_sin_theta B (C - B) hB (hB.add hE) k hk δ hδ
    (by rw [hgapB] at hδle; linarith)
  rw [initialProjector_congr (by abel : B + (C - B) = C) (hB.add hE) hC k] at hdk
  exact hdk

/-!
## High-probability projector drift for event streams (derived)
-/

/-- High-probability projector drift: for a random event-driven stream
whose Laplacian increments form a matrix martingale difference sequence
with uniform bound `R`, whose base Laplacian `L_0` has spectral gap at
least `γ` at index `k`, and for any `0 < s < γ`, the invariant-subspace
projector drift between the endpoints obeys
`P {‖P_{L_m} − P_{L_0}‖ ≥ s / (γ − s)} ≤ 2 d exp (−s² / (8 m R²))`,
where `d = card V`.

Dependency status: derived theorem. It combines `eventStreamTail` (itself
derived from `matrix_azuma_hoeffding`) with `davisKahanTwoPoint` (derived
from `davis_kahan_sin_theta` and the proved `weyl_inequality`, retired
from axiom on 2026-08-20). The conclusion is conditional on the two
remaining axioms and is not a foundationally proved result.

The shape answers the cumulative-vs-per-step interface question: the
bound is a *two-endpoint* statement with the probabilistic input entering
only through `‖L_m − L_0‖`, avoiding the crude deterministic
`m ε / γ` summation.

QA: exercised by `eventStreamProjectorDrift_constant_QA` in
`Scaffold/QA/Derived/ProjectorDrift_QA.lean` (constant stream under a
positive-gap hypothesis; the drift event is empty).
-/
theorem eventStreamProjectorDrift {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A : Ω → TimeVaryingGraph V)
    (R : ℝ)
    (h_adapt : ∀ k, StronglyMeasurable[mdsFiltration (randomLaplacianIncrement A) (k + 1)]
      (randomLaplacianIncrement A k))
    (h_cond : ∀ k S, MeasurableSet[mdsFiltration (randomLaplacianIncrement A) k] S →
      ∫ ω in S, randomLaplacianIncrement A k ω ∂μ = 0)
    (h_bound : ∀ k ω, ‖randomLaplacianIncrement A k ω‖ ≤ R)
    (hsymm : ∀ ω t, (A ω t).IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (γ : ℝ) (hγ : 0 < γ)
    (hgap : ∀ ω, spectralGap (laplacianSequence (A ω) 0)
      (laplacianSequence_symmetric (A ω) (hsymm ω) 0) k hk ≥ γ)
    (s : ℝ) (hs : 0 < s) (hsg : s < γ) (m : ℕ) :
    μ {ω | ‖initialProjector (laplacianSequence (A ω) m)
            (laplacianSequence_symmetric (A ω) (hsymm ω) m) k
          - initialProjector (laplacianSequence (A ω) 0)
            (laplacianSequence_symmetric (A ω) (hsymm ω) 0) k‖ ≥ s / (γ - s)} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(s ^ 2) / (8 * (m : ℝ) * R ^ 2))) := by
  have hincl : {ω : Ω | ‖initialProjector (laplacianSequence (A ω) m)
        (laplacianSequence_symmetric (A ω) (hsymm ω) m) k
        - initialProjector (laplacianSequence (A ω) 0)
          (laplacianSequence_symmetric (A ω) (hsymm ω) 0) k‖ ≥ s / (γ - s)}
      ⊆ {ω : Ω | ‖laplacianSequence (A ω) m - laplacianSequence (A ω) 0‖ ≥ s} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hlt
    have hnorm : ‖laplacianSequence (A ω) m - laplacianSequence (A ω) 0‖ < s :=
      lt_of_not_ge hlt
    have hδpos : 0 < γ - s := sub_pos.mpr hsg
    have hdk := davisKahanTwoPoint (laplacianSequence (A ω) 0)
      (laplacianSequence (A ω) m)
      (laplacianSequence_symmetric (A ω) (hsymm ω) 0)
      (laplacianSequence_symmetric (A ω) (hsymm ω) m) k hk (γ - s) hδpos
      (by
        have hg := hgap ω
        linarith)
    have hkey : ‖laplacianSequence (A ω) m - laplacianSequence (A ω) 0‖
        / (γ - s) < s / (γ - s) := by
      rw [div_lt_div_iff₀ hδpos hδpos]
      exact mul_lt_mul_of_pos_right hnorm hδpos
    exact absurd hω (by linarith)
  -- `eventStreamTail` (post-2026-08-28 repair) carries the `[Nonempty V]`
  -- guard the Azuma axiom now makes explicit; here it is derived from the
  -- theorem's own spectral-index hypothesis `k : Fin (Fintype.card V)`.
  haveI : Nonempty V := ⟨(Fintype.equivFin V).symm k⟩
  exact le_trans (measure_mono hincl)
    (eventStreamTail A R h_adapt h_cond h_bound m s hs.le)

end SpectralGraphTheory.Derived
