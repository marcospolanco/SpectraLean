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
import Scaffold.Mathlib.GraphTheory.Cheeger

/-!
# Random-walk interfaces for regular graphs

The first broad-SGT increment: the random-walk (Markov) view of a regular
weighted graph, bridged to both existing representations of the center —

- the combinatorial Laplacian `SpectralGraphTheory.laplacian`, through
  the scaling identity `randomWalkLaplacian = d⁻¹ • laplacian`;
- the symmetric normalized Laplacian of the Cheeger bridge, through the
  identity `randomWalkLaplacian = regularNormalizedLaplacian` (which
  holds for `d`-regular graphs, where the two normalizations coincide).

Everything here is proved; no axiom is admitted. The statements are
restricted to `d`-regular graphs because that is where the walk
Laplacian `I - D⁻¹A` is representable without a matrix square root
(the irregular symmetric normalization `I - D^{-1/2} A D^{-1/2}` needs
one, and the pinned Mathlib has none); see the SGT backlog for the
irregular-adapter plan.
-/

namespace SpectralGraphTheory

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Transition matrix
-/

/-- The random-walk transition matrix of a `d`-regular weighted graph:
`P = d⁻¹ • A`. For `deg A i = d` with `0 < d` this is row-stochastic
(`transitionMatrix_row_sum`), i.e. the transition kernel of the simple
random walk on the graph. Noncomputable because `ℝ` inversion is. -/
noncomputable def transitionMatrix (A : WAdj (V := V)) (d : ℝ) :
    Matrix V V ℝ :=
  d⁻¹ • A

/-- The transition matrix of a symmetric adjacency matrix is symmetric. -/
theorem transitionMatrix_symmetric (A : WAdj (V := V))
    (hA : A.IsSymm) (d : ℝ) :
    (transitionMatrix A d).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [transitionMatrix, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hA.apply i j]

/-- Row-stochasticity: for a `d`-regular graph with positive degree `d`,
every row of the transition matrix sums to one. This is the interface a
Markov-chain consumer needs: `P i ·` is a probability distribution. -/
theorem transitionMatrix_row_sum (A : WAdj (V := V))
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d) (i : V) :
    ∑ j, transitionMatrix A d i j = 1 := by
  simp only [transitionMatrix, Matrix.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]
  rw [← deg, hd i, inv_mul_cancel₀ (ne_of_gt hdpos)]

/-!
## Walk Laplacian and its bridges
-/

/-- The random-walk Laplacian `L_rw = I - P`. For a `d`-regular graph
this coincides with the symmetric normalized Laplacian of the Cheeger
bridge (`randomWalkLaplacian_eq_regularNormalizedLaplacian`) and is a
scalar multiple of the combinatorial Laplacian
(`randomWalkLaplacian_eq_smul_laplacian`). Noncomputable because `ℝ`
inversion is. -/
noncomputable def randomWalkLaplacian (A : WAdj (V := V)) (d : ℝ) : Matrix V V ℝ :=
  1 - transitionMatrix A d

/-- The walk Laplacian of a symmetric adjacency matrix is symmetric. -/
theorem randomWalkLaplacian_symmetric (A : WAdj (V := V))
    (hA : A.IsSymm) (d : ℝ) :
    (randomWalkLaplacian A d).IsSymm :=
  isSymm_one.sub (transitionMatrix_symmetric A hA d)

/-- Interoperability with the Cheeger bridge: for a `d`-regular graph
the walk Laplacian *is* the symmetric normalized Laplacian — the two
normalizations coincide exactly on the regular cone. This connects the
Markov view of this module to the Cheeger inequalities, which are stated
through `regularNormalizedLaplacian`. -/
theorem randomWalkLaplacian_eq_regularNormalizedLaplacian
    (A : WAdj (V := V)) (d : ℝ) :
    randomWalkLaplacian A d = regularNormalizedLaplacian A d := rfl

/-- Bridge to the combinatorial center: for a `d`-regular graph with
positive degree, the walk Laplacian is `d⁻¹` times the combinatorial
Laplacian. Consequences (spectral and quadratic-form statements about
`laplacian`) transfer to the walk view by homogeneity in `d⁻¹ > 0`. -/
theorem randomWalkLaplacian_eq_smul_laplacian (A : WAdj (V := V))
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d) :
    randomWalkLaplacian A d = d⁻¹ • laplacian A := by
  ext i j
  simp only [randomWalkLaplacian, transitionMatrix, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, Pi.one_apply,
    laplacian, degreeMatrix]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, dif_pos rfl, hd i]
    field_simp
  · simp [h]

end SpectralGraphTheory
