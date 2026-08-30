/-
  ProjectorDrift_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Derived.ProjectorDrift`: the two-point
  Davis–Kahan wrapper instantiated at `C = B`, and the high-probability
  projector-drift theorem instantiated at a constant (zero-increment)
  stream under a positive spectral-gap hypothesis.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not prove
  the underlying Davis–Kahan, Weyl, or Matrix Azuma axioms; the derived
  statements remain conditional on them.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Derived.ProjectorDrift

open MeasureTheory ProbabilityTheory
open Scaffold.Mathlib.Probability.Concentration.Matrix
open scoped Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory.Derived.QA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Two-point wrapper
-/

/-- The two-point wrapper at `C = B` with `δ` equal to the spectral gap:
the perturbation is zero, so the bound degenerates to `‖0‖ ≤ 0 / gap`.
Exercises the gap-hypothesis interface (`gap ≤ gap − ‖B − B‖`). -/
theorem davisKahanTwoPoint_self_QA (B : Matrix V V ℝ) (hB : B.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (hδ : 0 < spectralGap B hB k hk) :
    ‖initialProjector B hB k - initialProjector B hB k‖
      ≤ ‖B - B‖ / spectralGap B hB k hk :=
  davisKahanTwoPoint B B hB hB k hk _ hδ
    (by simp)

/-!
## Derived projector drift
-/

/-- The constant random stream used for degenerate instantiation. -/
def constantStream (G : Matrix V V ℝ) : Ω → TimeVaryingGraph V :=
  fun _ _ => G

/-- Constant streams have identically zero Laplacian increments. -/
theorem constantStream_increment_zero_QA (G : Matrix V V ℝ) (k : ℕ) (ω : Ω) :
    randomLaplacianIncrement (constantStream G) k ω = 0 := by
  simp [randomLaplacianIncrement, constantStream, laplacianSequence]

/-- The derived drift theorem instantiated at a constant stream with bound
`R = 0` under a positive base-gap hypothesis: all martingale hypotheses
are discharged constructively and the conclusion is the degenerate Azuma
bound. -/
theorem eventStreamProjectorDrift_constant_QA (G : Matrix V V ℝ) (hG : G.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (γ s : ℝ) (hγ : 0 < γ) (hs : 0 < s) (hsg : s < γ)
    (hgap : γ ≤ spectralGap (laplacian G) (laplacian_symmetric G hG) k hk)
    (m : ℕ) :
    μ {ω | ‖initialProjector (laplacianSequence (constantStream G ω) m)
        (laplacianSequence_symmetric (constantStream G ω) (fun _ => hG) m) k
        - initialProjector (laplacianSequence (constantStream G ω) 0)
          (laplacianSequence_symmetric (constantStream G ω) (fun _ => hG) 0) k‖
        ≥ s / (γ - s)} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(s ^ 2) / (8 * (m : ℝ) * (0 : ℝ) ^ 2))) :=
  eventStreamProjectorDrift (constantStream G) 0
    (fun k' => by
      have h0 : randomLaplacianIncrement (constantStream (Ω := Ω) G) k'
          = fun _ => 0 :=
        funext (constantStream_increment_zero_QA G k')
      rw [h0]
      exact stronglyMeasurable_const)
    (fun k' S _ => by
      have h0 : randomLaplacianIncrement (constantStream (Ω := Ω) G) k'
          = fun _ => 0 :=
        funext (constantStream_increment_zero_QA G k')
      rw [h0]
      simp)
    (fun k' ω => by
      rw [constantStream_increment_zero_QA]
      simp)
    (fun _ _ => hG) k hk γ hγ
    (fun ω => by simpa [constantStream, laplacianSequence] using hgap)
    s hs hsg m

/-- The constant-stream drift event is empty (both endpoint projectors
coincide), so its measure is exactly `0`: the degenerate case of the
derived bound is tight. -/
theorem eventStreamProjectorDrift_constant_event_QA (G : Matrix V V ℝ)
    (hG : G.IsSymm) (k : Fin (Fintype.card V))
    {γ s : ℝ} (hs : 0 < s) (hsg : s < γ) :
    μ {ω | ‖initialProjector (laplacianSequence (constantStream G ω) 1)
        (laplacianSequence_symmetric (constantStream G ω) (fun _ => hG) 1) k
        - initialProjector (laplacianSequence (constantStream G ω) 0)
          (laplacianSequence_symmetric (constantStream G ω) (fun _ => hG) 0) k‖
        ≥ s / (γ - s)} = 0 := by
  have ht : 0 < s / (γ - s) := div_pos hs (sub_pos.mpr hsg)
  have hempty : {ω : Ω | ‖initialProjector (laplacianSequence (constantStream G ω) 1)
        (laplacianSequence_symmetric (constantStream G ω) (fun _ => hG) 1) k
        - initialProjector (laplacianSequence (constantStream G ω) 0)
          (laplacianSequence_symmetric (constantStream G ω) (fun _ => hG) 0) k‖
        ≥ s / (γ - s)} = ∅ := by
    ext ω
    have hpr : initialProjector (laplacianSequence (constantStream G ω) 1)
        (laplacianSequence_symmetric (constantStream G ω) (fun _ => hG) 1) k
        = initialProjector (laplacianSequence (constantStream G ω) 0)
          (laplacianSequence_symmetric (constantStream G ω) (fun _ => hG) 0) k :=
      initialProjector_congr (rfl) _ _ k
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, hpr, sub_self, norm_zero]
    simp [ht.not_le]
  rw [hempty, measure_empty]

end SpectralGraphTheory.Derived.QA
