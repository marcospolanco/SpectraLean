/-
  EventStream_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Derived.EventStream`: the telescoping identity,
  the boundedness/event-driven interface lemma, and the derived tail
  theorem instantiated at a constant (zero-increment) stream.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not prove
  the underlying Matrix Azuma axiom; the derived tail theorem remains
  conditional on it.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Derived.EventStream

open MeasureTheory ProbabilityTheory
open Scaffold.Mathlib.Probability.Concentration.Matrix
open scoped Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory.Derived.QA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The constant random stream: every realization is the same static
graph, so every Laplacian increment is zero. -/
def constantStream (G : Matrix V V ℝ) : Ω → TimeVaryingGraph V :=
  fun _ _ => G

/-!
## Deterministic core
-/

/-- Telescoping at `m = 0`: the empty sum is the trivial drift. -/
theorem telescope_zero_QA (L : ℕ → Matrix V V ℝ) :
    ∑ k in Finset.range 0, (L (k + 1) - L k) = L 0 - L 0 := by
  simp [sum_range_telescope]

/-- Telescoping at `m = 1`: a single increment equals the endpoint
difference. -/
theorem telescope_one_QA (L : ℕ → Matrix V V ℝ) :
    ∑ k in Finset.range 1, (L (k + 1) - L k) = L 1 - L 0 :=
  sum_range_telescope L 1

/-!
## Interface identification
-/

/-- A constant stream has identically zero increments. -/
theorem constantStream_increment_zero_QA (G : Matrix V V ℝ) (k : ℕ) (ω : Ω) :
    randomLaplacianIncrement (constantStream G) k ω = 0 := by
  simp [randomLaplacianIncrement, constantStream, laplacianSequence]

/-- Through the interface lemma, every realization of a constant stream is
event-driven with bound `0` — the deterministic dynamics interface and
the probabilistic increment interface agree on the degenerate case. -/
theorem constantStream_isEventDriven_zero_QA (G : Matrix V V ℝ) (ω : Ω) :
    IsEventDriven (constantStream G ω) 0 := by
  refine (randomLaplacianIncrement_bounded_iff (constantStream G) 0).1 ?_ ω
  intro k ω'
  rw [constantStream_increment_zero_QA]
  simp

/-!
## Derived tail bound
-/

/-- Ambient strong measurability of the constant stream (the repaired
`h_meas` clause shape): every increment is the constant `0`. -/
theorem constantStream_meas_QA (G : Matrix V V ℝ) (k : ℕ) :
    StronglyMeasurable[mΩ] (randomLaplacianIncrement (constantStream (Ω := Ω) G) k) := by
  have h0 : randomLaplacianIncrement (constantStream (Ω := Ω) G) k = fun _ => 0 :=
    funext (constantStream_increment_zero_QA G k)
  rw [h0]
  exact stronglyMeasurable_const

/-- The derived tail theorem instantiated at a constant stream with bound
`R = 0`: all martingale hypotheses are discharged constructively and the
conclusion is the degenerate Azuma bound. -/
theorem eventStreamTail_constant_QA [Nonempty V] (G : Matrix V V ℝ) (m : ℕ) (t : ℝ) (ht : 0 < t) :
    μ {ω | ‖laplacianSequence (constantStream G ω) m
        - laplacianSequence (constantStream G ω) 0‖ ≥ t} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (8 * (m : ℝ) * (0 : ℝ) ^ 2))) :=
  eventStreamTail (constantStream G) 0
    (fun k => constantStream_meas_QA G k)
    (fun k S _ => by
      have h0 : randomLaplacianIncrement (constantStream (Ω := Ω) G) k = fun _ => 0 :=
        funext (constantStream_increment_zero_QA G k)
      rw [h0]
      simp)
    (fun k ω => by
      rw [constantStream_increment_zero_QA]
      simp)
    m t ht.le

/-- The constant-stream cumulative perturbation is identically zero, so
the tail event is empty and its measure is exactly `0`: the degenerate
case of the derived bound is tight. -/
theorem eventStreamTail_constant_event_QA (G : Matrix V V ℝ) {m : ℕ} {t : ℝ}
    (ht : 0 < t) :
    μ {ω | ‖laplacianSequence (constantStream G ω) m
        - laplacianSequence (constantStream G ω) 0‖ ≥ t} = 0 := by
  have hempty : {ω : Ω | ‖laplacianSequence (constantStream G ω) m
      - laplacianSequence (constantStream G ω) 0‖ ≥ t} = ∅ := by
    ext ω
    simp only [constantStream, laplacianSequence, sub_self, norm_zero]
    simp [ht.not_le]
  rw [hempty, measure_empty]

end SpectralGraphTheory.Derived.QA
