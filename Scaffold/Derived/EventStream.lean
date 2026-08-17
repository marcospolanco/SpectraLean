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
import Scaffold.Mathlib.GraphTheory.Dynamics
import Scaffold.Mathlib.Probability.Concentration.Matrix.Azuma

/-!
# Event-stream tail bound (derived layer)

First inhabitants of the derived layer: an axiom-backed theorem connecting
the dynamic-persistence frontier (`SpectralGraphTheory.IsEventDriven`) to
the matrix-concentration bridge
(`Probability.Concentration.Matrix.matrix_azuma_hoeffding`).

The deterministic content is proved: the telescoping identity
`∑_{k < m} (L_{k+1} - L_k) = L_m - L_0`, and the identification of the
uniform increment bound with the pointwise `IsEventDriven` condition.

The tail statement itself is a derived theorem: the proof combines the
telescoping identity (proved here) with the admitted Matrix Azuma axiom
(Tropp 2012, Theorem 7.1). It is conditional on that axiom and is not a
foundationally proved result; the axiom remains the visible trust
boundary. This is the probabilistic half of the `‖Σₖ Eₖ‖ / γ`
persistence hypothesis; combining it with the Davis–Kahan bridge is the
next derivation.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory.Derived

open Scaffold.Mathlib.Probability.Concentration.Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Deterministic core (proved)
-/

/-- Telescoping identity: the sum of consecutive increments of a sequence
in an additive abelian group equals the endpoint difference. Used to
convert a cumulative perturbation sum into a two-point Laplacian
difference. -/
theorem sum_range_telescope {G : Type*} [AddCommGroup G] (f : ℕ → G) (m : ℕ) :
    ∑ k in Finset.range m, (f (k + 1) - f k) = f m - f 0 := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- The random Laplacian increment process of a random time-varying
graph `A : Ω → TimeVaryingGraph V`: the matrix event
`E k ω = L_{k+1}(ω) - L_k(ω)` applied at time `k`. -/
def randomLaplacianIncrement {Ω : Type*} (A : Ω → TimeVaryingGraph V) (k : ℕ) :
    Ω → Matrix V V ℝ :=
  fun ω => laplacianSequence (A ω) (k + 1) - laplacianSequence (A ω) k

/-- Interface identification: a uniform norm bound `R` on the increment
process is exactly the pointwise event-driven condition
`IsEventDriven (A ω) R` on every realization. This is the compatibility
check between the deterministic dynamics interface and the probabilistic
concentration interface. -/
theorem randomLaplacianIncrement_bounded_iff {Ω : Type*}
    (A : Ω → TimeVaryingGraph V) (R : ℝ) :
    (∀ k ω, ‖randomLaplacianIncrement A k ω‖ ≤ R) ↔ ∀ ω, IsEventDriven (A ω) R := by
  constructor
  · intro h ω t
    exact h t ω
  · intro h k ω
    exact h ω k

/-!
## Derived tail bound (axiom-backed)

`eventStreamTail` is proved from the admitted Matrix Azuma inequality; it
is correct *relative to that axiom*, not foundationally.
-/

/-- Event-stream tail bound: for a random time-varying graph whose
Laplacian increments form a matrix martingale difference sequence with
uniform spectral-norm bound `R` (in particular every realization is
`R`-event-driven, by `randomLaplacianIncrement_bounded_iff`), the
cumulative Laplacian perturbation after `m` steps obeys
`P {‖L_m - L_0‖ ≥ t} ≤ 2 d exp (-t² / (8 m R²))`, where `d = card V`.

Dependency status: derived theorem. The telescoping step is proved
(`sum_range_telescope`); the tail bound is the admitted Matrix Azuma
inequality (`matrix_azuma_hoeffding`, Tropp 2012, Theorem 7.1). The
conclusion is conditional on that axiom.

QA: exercised by `eventStreamTail_constant_QA` and
`eventStreamTail_constant_event_QA` in
`Scaffold/QA/Derived/EventStream_QA.lean`, which instantiate the theorem
at a constant (zero-increment) stream.
-/
theorem eventStreamTail {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A : Ω → TimeVaryingGraph V) (R : ℝ)
    (h_adapt : ∀ k, StronglyMeasurable[mdsFiltration (randomLaplacianIncrement A) (k + 1)]
      (randomLaplacianIncrement A k))
    (h_cond : ∀ k S, MeasurableSet[mdsFiltration (randomLaplacianIncrement A) k] S →
      ∫ ω in S, randomLaplacianIncrement A k ω ∂μ = 0)
    (h_bound : ∀ k ω, ‖randomLaplacianIncrement A k ω‖ ≤ R)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | ‖laplacianSequence (A ω) m - laplacianSequence (A ω) 0‖ ≥ t} ≤
      ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-t ^ 2 / (8 * (m : ℝ) * R ^ 2))) := by
  have hazuma := matrix_azuma_hoeffding m
    (⟨R, randomLaplacianIncrement A, h_adapt, h_cond, h_bound⟩ :
      MatrixMDS (V := V) μ) t ht
  have hset : {ω | ‖laplacianSequence (A ω) m - laplacianSequence (A ω) 0‖ ≥ t}
      = {ω | ‖∑ k in Finset.range m, randomLaplacianIncrement A k ω‖ ≥ t} := by
    ext ω
    simp only [randomLaplacianIncrement, sum_range_telescope]
  rw [hset]
  exact hazuma

end SpectralGraphTheory.Derived
