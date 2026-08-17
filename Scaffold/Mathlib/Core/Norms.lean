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

/-!
# Shared norm utilities

This module defines the pointwise `L∞` size used by the scalar and matrix
concentration interfaces. It is a real definition: the infimum of all uniform
bounds on `|X ω|` over every outcome `ω`.

Note: this is an everywhere-supremum quantity, not a measure-theoretic
essential supremum. For finite sample spaces (the setting of current
Scaffold consumers) the two coincide; passing to `essSup` is deferred until
a consumer needs genuinely negligible-measure exceptions.
-/

namespace Scaffold.Mathlib.Core

open MeasureTheory

/-- The pointwise `L∞` size of a real random variable `X`:
`sInf {M | 0 ≤ M ∧ ∀ ω, |X ω| ≤ M}`.

For a bounded variable this is `sup_ω |X ω|`; for an unbounded variable the
index set is empty and the `sInf` is `0`. The empty case is a junk value, as
is standard for `sInf ∅` in `ℝ`; consumers must establish boundedness. -/
noncomputable def l_infty_norm {Ω : Type*} [MeasurableSpace Ω] (X : RV Ω) : ℝ :=
  sInf {M : ℝ | 0 ≤ M ∧ ∀ ω, |X ω| ≤ M}

/-- A bounded variable has nonnegative pointwise `L∞` size: `0` is an
admissible uniform bound. -/
theorem l_infty_norm_nonneg {Ω : Type*} [MeasurableSpace Ω] (X : RV Ω) :
    0 ≤ l_infty_norm X :=
  Real.sInf_nonneg fun M hM => hM.1

end Scaffold.Mathlib.Core
