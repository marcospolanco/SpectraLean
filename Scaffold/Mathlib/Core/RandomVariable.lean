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
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic

namespace Scaffold.Mathlib.Core

/-
A real-valued random variable on a measurable space.

This is a minimal alias for measurable functions from a sample space to ℝ.
We use mathlib's MeasureTheory and ProbabilityTheory infrastructure.

Intended meaning:
For a measurable space `Ω`, a random variable is a measurable function `X : Ω → ℝ`.
This matches the standard measure-theoretic definition of a random variable.
-/
def RV (Ω : Type*) [MeasurableSpace Ω] := Ω → ℝ

/-
A matrix-valued random variable on a measurable space.

Intended meaning:
For a measurable space `Ω` and a finite index set `V`,
a matrix random variable is a measurable function `X : Ω → Matrix V V ℝ`.
-/
def MRV (Ω : Type*) [MeasurableSpace Ω] (V : Type*) [Fintype V] [DecidableEq V] :=
  Ω → Matrix V V ℝ

end Scaffold.Mathlib.Core