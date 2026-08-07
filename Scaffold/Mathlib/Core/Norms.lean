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
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Scaffold.Mathlib.Core.RandomVariable

namespace Scaffold.Mathlib.Core

/-
Shared norm definitions and properties for concentration inequalities.

This module provides common norm definitions used across concentration inequalities.
We re-export mathlib's norm infrastructure and add Scaffold-specific notation.
-/

open Mathlib

/-
The L∞ norm (essential supremum) of a random variable.

This is defined as the infimum of all M such that |X| ≤ M almost surely.
-/
def l_infty_norm {Ω : Type*} [MeasureSpace Ω] [ZeroOmega] (X : RV Ω) : ℝ :=
  sInf {M : ℝ | 0 ≤ M ∧ ∀ ω, |X ω| ≤ M}

end Scaffold.Mathlib.Core