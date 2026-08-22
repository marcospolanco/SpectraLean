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
import Scaffold.Mathlib.GraphTheory.Stationary

/-!
# The ℓ²-mixing proxy of the simple random walk

Step 2 of the mixing-time program
(`proposals/mixing-time-bound.md`): the mixing-distance object that
Step 3's geometric decay bound quantifies, with its evolution
interface — no measure-theoretic definitions, everything stated
through the `deg`/`vol`/`walkTransitionMatrix` machinery of the
center.

**Scoping record (the proposal's decide-and-record gate, made before
any statement):** the ℓ² statement alone satisfies this proposal's
goal; the ℓ² → TV conversion stays a separate further step (the
proposal's own Step 4 framing). Within ℓ², the *weighted* form is
primary: the proxy is the χ² distance
`χ²(t, x) = ∑ i, (ν_t i − π i)² / π i` with `π = deg/vol`, because the
decay bound of Step 3 is Parseval-exact in the π-weighted inner
product — the only inner product in which the transferred eigenbasis
of Step 1 (`walkTransitionMatrix_mulVec_eigvecOf`) is orthogonal. The
unweighted Euclidean distance of the proposal's original sketch is
delivered as the corollary bridge
`sum_sub_sq_walkDistribution_le` rather than as the primary object.

The declarations:

- `stationaryVec`: the stationary distribution `π i = deg A i / vol A`
  in vector form — strictly positive for positive degrees on a
  nonempty vertex type (`stationaryVec_pos`) and summing to one
  (`sum_stationaryVec`); `walk_isStationary` restates the proved
  degree-form stationarity at `π`.
- `walkDistribution`: the law of the walk started at `x` after `t`
  steps, `(Pᵀ)ᵗ *ᵥ δₓ`, with the evolution equations
  (`walkDistribution_zero`, `walkDistribution_succ`) and conservation
  of mass (`sum_walkDistribution`).
- `walkDensity`: the density `ν_t/π` — the coordinate in which the
  walk acts by `walkTransitionMatrix` itself (`walkDensity_succ`,
  *via detailed balance*: the first consumer of the Phase A interface
  `walk_detailed_balance_measure`), hence the coordinate Step 3
  expands on the transferred eigenbasis.
- `chiSquareDistance`: the χ² mixing distance itself, with
  nonnegativity, the vanishing characterization
  `chiSquareDistance_eq_zero_iff`, the `t = 0` value
  `(π x)⁻¹ − 1` (Step 3's normalization constant), the density-form
  equivalence `chiSquareDistance_eq_sum_smul`, and the plain-ℓ²
  corollary bridge `sum_sub_sq_walkDistribution_le`.
- the **geometric decay engine** (Step 3, component 1): eigencoordinate
  evolution under walk powers
  (`eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix`),
  the Parseval-exact decay identity
  (`dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix`), the
  ℓ²(π) contraction in conjugated-norm and mixing forms
  (`..._le`, `sum_stationaryVec_smul_sq_pow_walkTransitionMatrix_le`)
  under value-based mode/rate hypotheses, and the π-norm bridge
  (`sum_stationaryVec_smul_sq_eq`).
- the **χ² assembly** (Step 3, component 2 — the program's closing
  statement): the centered density evolution `walkDensity_sub_one`
  (`h_t − 1 = Pᵗ *ᵥ (h₀ − 1)`), mass conservation in the conjugated
  pairing (`sum_deg_mul_walkDensity_sub_one_eq_zero`), the connectivity
  mode derivation
  (`eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero`
  — the kernel of `L_sym` on a connected graph, through the congruence,
  composed with mass conservation), and the headline mixing bound
  `chiSquareDistance_le_of_connected`:
  `χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)` under the rate hypothesis.

Everything here is proved; no axiom is admitted. The pinned Mathlib
has no chi-square, total-variation, or mixing-time objects (surveyed
2026-08-22; `docs/8_MATHLIB_COVERAGE_MAP.md` records the upstream
absence), so this module is original Scaffold surface.
-/

namespace SpectralGraphTheory

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## The stationary distribution in vector form
-/

/-- The stationary distribution of the simple random walk on a graph
with positive degrees, as a vector: `π i = deg A i / vol A univ`.
Certified stationary by `walk_isStationary` (the probability-measure
packaging of the proved `walkTransitionMatrix_transpose_mulVec_deg`);
strictly positive entrywise for positive degrees on a nonempty vertex
type (`stationaryVec_pos`) and sums to one (`sum_stationaryVec`).
Noncomputable because real division is. -/
noncomputable def stationaryVec (A : WAdj (V := V)) : V → ℝ :=
  fun i => deg A i / vol A (Finset.univ : Finset V)

omit [DecidableEq V] in
/-- The total volume of a graph with positive degrees on a nonempty
vertex type is positive. Support lemma for the strict positivity of
`stationaryVec`. -/
theorem vol_univ_pos (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] :
    0 < vol A (Finset.univ : Finset V) :=
  Finset.sum_pos' (fun i _ => le_of_lt (hd i))
    ⟨‹Nonempty V›.some, Finset.mem_univ _, hd _⟩

omit [DecidableEq V] in
/-- The stationary distribution is strictly positive entrywise
(positive degrees, nonempty vertex type). This is the hypothesis that
makes every division by `stationaryVec A i` in the χ² layer
meaningful. -/
theorem stationaryVec_pos (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (i : V) :
    0 < stationaryVec A i :=
  div_pos (hd i) (vol_univ_pos A hd)

omit [DecidableEq V] in
/-- The stationary distribution sums to one — it really is a
probability vector. -/
theorem sum_stationaryVec (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] :
    ∑ i, stationaryVec A i = 1 := by
  simp only [stationaryVec]
  rw [← Finset.sum_div,
    show (∑ i, deg A i) = vol A (Finset.univ : Finset V) from rfl,
    div_self (ne_of_gt (vol_univ_pos A hd))]

omit [DecidableEq V] in
/-- Unpacking: the stationary vector is the degree vector rescaled by
the inverse total volume. -/
theorem stationaryVec_eq_inv_smul_deg (A : WAdj (V := V)) :
    stationaryVec A
      = (vol A (Finset.univ : Finset V))⁻¹ • deg A := by
  funext i
  simp only [stationaryVec, Pi.smul_apply, smul_eq_mul,
    div_eq_inv_mul]

/-- The stationary distribution packaged at `π = deg/vol`: the adjoint
walk fixes `π`. This is the probability-measure form of the proved
`walkTransitionMatrix_transpose_mulVec_deg` (degree form), obtained by
rescaling, and the statement a mixing consumer starts from: the
`t → ∞` candidate of `walkDistribution`. -/
theorem walk_isStationary (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) :
    (walkTransitionMatrix A)ᵀ *ᵥ stationaryVec A = stationaryVec A := by
  rw [stationaryVec_eq_inv_smul_deg, Matrix.mulVec_smul,
    walkTransitionMatrix_transpose_mulVec_deg A hA hd]

/-!
## The walk distribution and its evolution
-/

/-- The distribution of the simple random walk started at `x` after
`t` steps: `(Pᵀ)ᵗ *ᵥ δₓ` with `P = D⁻¹A` the row-stochastic walk
transition matrix (the adjoint action is the distributional one: the
law at `t + 1` is `Pᵀ *ᵥ` the law at `t`, `walkDistribution_succ`).
At `t = 0` this is the point mass itself (`walkDistribution_zero`);
mass is conserved at every step (`sum_walkDistribution`). Noncomputable
because `walkTransitionMatrix` is. -/
noncomputable def walkDistribution (A : WAdj (V := V)) (t : ℕ) (x : V) :
    V → ℝ :=
  ((walkTransitionMatrix A)ᵀ ^ t) *ᵥ (Pi.single x (1 : ℝ))

/-- At time zero the walk sits at its start: `ν₀ = δₓ`. -/
theorem walkDistribution_zero (A : WAdj (V := V)) (x : V) :
    walkDistribution A 0 x = Pi.single x (1 : ℝ) := by
  simp only [walkDistribution]
  rw [pow_zero, Matrix.one_mulVec]

/-- The evolution equation: one more step applies the adjoint walk to
the current law. -/
theorem walkDistribution_succ (A : WAdj (V := V)) (t : ℕ) (x : V) :
    walkDistribution A (t + 1) x
      = (walkTransitionMatrix A)ᵀ *ᵥ walkDistribution A t x := by
  simp only [walkDistribution]
  rw [pow_succ', ← Matrix.mulVec_mulVec]

/-- Conservation of mass: the law of the walk is a probability vector
at every time. Load-bearing on the row-stochasticity of
`walkTransitionMatrix` (`walkTransitionMatrix_row_sum`). -/
theorem sum_walkDistribution (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i)
    (t : ℕ) (x : V) :
    ∑ i, walkDistribution A t x i = 1 := by
  have hstep : ∀ ν : V → ℝ,
      ∑ i, ((walkTransitionMatrix A)ᵀ *ᵥ ν) i = ∑ i, ν i := by
    intro ν
    simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, walkTransitionMatrix_row_sum A hd j, one_mul]
  induction t with
  | zero =>
    rw [walkDistribution_zero]
    simp [Pi.single_apply]
  | succ t ih => rw [walkDistribution_succ, hstep, ih]

/-!
## The density: the coordinate the eigenbasis diagonalizes
-/

/-- The density of the walk law with respect to the stationary
distribution: `h_t i = ν_t i / π i`. This is the coordinate in which
the walk acts by `walkTransitionMatrix` *itself*
(`walkDensity_succ`, via detailed balance) rather than by its adjoint,
and therefore the coordinate in which the transferred eigenbasis of
Step 1 diagonalizes the evolution — Step 3 expands `h_t − 1` on that
basis. Junk value `0` wherever `π i = 0` (positive degrees rule that
out). Noncomputable because real division is. -/
noncomputable def walkDensity (A : WAdj (V := V)) (t : ℕ) (x : V) :
    V → ℝ :=
  fun i => walkDistribution A t x i / stationaryVec A i

/-- **The density evolution equation**: `h_{t+1} = P *ᵥ h_t`. In
density coordinates the distributional evolution (`Pᵀ` on laws)
becomes the action of `P` itself — this is detailed balance in
action, and the first consumer of the Phase A interface
`walk_detailed_balance_measure`. This is the interface Step 3
consumes: the transferred eigenbasis of `walkTransitionMatrix` (Step 1)
now governs the mixing evolution directly. -/
theorem walkDensity_succ (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    walkDensity A (t + 1) x
      = walkTransitionMatrix A *ᵥ walkDensity A t x := by
  have hpos : ∀ i, stationaryVec A i ≠ 0 := fun i =>
    ne_of_gt (stationaryVec_pos A hd i)
  have hterm : ∀ (j i : V),
      walkTransitionMatrix A i j * walkDistribution A t x i
          / stationaryVec A j
      = walkTransitionMatrix A j i
          * (walkDistribution A t x i / stationaryVec A i) := by
    intro j i
    have hDB : stationaryVec A i * walkTransitionMatrix A i j
        = stationaryVec A j * walkTransitionMatrix A j i :=
      walk_detailed_balance_measure A hA hd i j
    have hπi := hpos i
    have hπj := hpos j
    rw [← mul_div_assoc, div_eq_div_iff hπj hπi]
    linear_combination walkDistribution A t x i * hDB
  funext j
  simp only [walkDensity]
  rw [walkDistribution_succ A t x]
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => hterm j i

/-!
## The χ² mixing distance
-/

/-- The χ² (weighted-ℓ²) mixing distance between the `t`-step walk law
and the stationary distribution:
`χ²(t, x) = ∑ i, (ν_t i − π i)² / π i` — the proposal's ℓ² proxy in
its weighted form (see the module docstring's scoping record: this is
the form in which Step 3's decay bound is Parseval-exact). Real
definition; the junk value at `π i = 0` is `0` by real division, and
every theorem carries the degree-positivity hypothesis ruling that
case out. The unweighted Euclidean distance is bounded through it by
`sum_sub_sq_walkDistribution_le`. Noncomputable because real division
is. -/
noncomputable def chiSquareDistance (A : WAdj (V := V)) (t : ℕ) (x : V) :
    ℝ :=
  ∑ i, (walkDistribution A t x i - stationaryVec A i)^2
    / stationaryVec A i

/-- The χ² distance is nonnegative (sum of squares weighted by a
positive measure). -/
theorem chiSquareDistance_nonneg (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    0 ≤ chiSquareDistance A t x :=
  Finset.sum_nonneg fun i _ =>
    div_nonneg (sq_nonneg _) (le_of_lt (stationaryVec_pos A hd i))

/-- Vanishing characterization: `χ²(t, x) = 0` exactly when the walk
law has reached the stationary distribution. The positivity of `π` is
load-bearing — at a zero-degree vertex the hypothesis-free form fails
(witnessed in QA). -/
theorem chiSquareDistance_eq_zero_iff (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    chiSquareDistance A t x = 0
      ↔ walkDistribution A t x = stationaryVec A := by
  constructor
  · intro h
    funext i
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => div_nonneg (sq_nonneg _)
        (le_of_lt (stationaryVec_pos A hd j)))).mp h i
      (Finset.mem_univ i)
    rw [div_eq_zero_iff] at hterm
    rcases hterm with h0 | h0
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h0)
    · exact absurd h0 (ne_of_gt (stationaryVec_pos A hd i))
  · intro h
    simp only [chiSquareDistance, h, sub_self]
    simp

/-- The `t = 0` value: starting from a point mass, the χ² distance is
`(π x)⁻¹ − 1` — the normalization constant of Step 3's decay bound
(the textbook sup over start vertices of this quantity is the standard
prefactor in the mixing estimate). -/
theorem chiSquareDistance_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (x : V) :
    chiSquareDistance A 0 x = (stationaryVec A x)⁻¹ - 1 := by
  have hπx : stationaryVec A x ≠ 0 :=
    ne_of_gt (stationaryVec_pos A hd x)
  have hmem : x ∈ (Finset.univ : Finset V) := Finset.mem_univ x
  have hon : (Pi.single x (1 : ℝ) : V → ℝ) x = 1 := by
    rw [Pi.single_apply, if_pos rfl]
  have hoff : ∀ i ∈ Finset.univ.erase x,
      ((Pi.single x (1 : ℝ) : V → ℝ) i - stationaryVec A i)^2
        / stationaryVec A i = stationaryVec A i := by
    intro i hi
    have hne : i ≠ x := Finset.ne_of_mem_erase hi
    have hπi : stationaryVec A i ≠ 0 :=
      ne_of_gt (stationaryVec_pos A hd i)
    have hsingle : (Pi.single x (1 : ℝ) : V → ℝ) i = 0 := by
      rw [Pi.single_apply, if_neg hne]
    have hsq : (0 - stationaryVec A i)^2
        = stationaryVec A i * stationaryVec A i := by ring
    rw [hsingle, hsq, mul_div_assoc, div_self hπi, mul_one]
  have hsplit : ∀ F : V → ℝ, ∑ i, F i
      = F x + ∑ i in Finset.univ.erase x, F i := by
    intro F
    rw [← Finset.insert_erase hmem,
      Finset.sum_insert (Finset.not_mem_erase x _)]
    simp
  have hrest : ∑ i in Finset.univ.erase x, stationaryVec A i
      = 1 - stationaryVec A x := by
    have h1 := hsplit (stationaryVec A)
    rw [sum_stationaryVec A hd] at h1
    linarith
  have herase : ∑ i in Finset.univ.erase x,
      ((Pi.single x (1 : ℝ) : V → ℝ) i - stationaryVec A i)^2
        / stationaryVec A i
      = 1 - stationaryVec A x := by
    rw [Finset.sum_congr rfl (fun i hi => hoff i hi), hrest]
  rw [chiSquareDistance, walkDistribution_zero,
    hsplit fun i =>
      ((Pi.single x (1 : ℝ) : V → ℝ) i - stationaryVec A i)^2
        / stationaryVec A i]
  rw [hon, Finset.sum_congr rfl (fun i hi => hoff i hi), hrest]
  have hfin : stationaryVec A x * (((1 - stationaryVec A x)^2
        / stationaryVec A x) + (1 - stationaryVec A x))
      = stationaryVec A x * ((stationaryVec A x)⁻¹ - 1) := by
    field_simp
    ring
  exact mul_left_cancel₀ hπx hfin

/-- The χ² distance in density form: `∑ i, π i * (h_t i − 1)²`, the
π-weighted inner product of the centered density with itself — the
exact quantity Step 3 computes by Parseval on the transferred
eigenbasis. -/
theorem chiSquareDistance_eq_sum_smul (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    chiSquareDistance A t x
      = ∑ i, stationaryVec A i * (walkDensity A t x i - 1)^2 := by
  have hpos : ∀ i, stationaryVec A i ≠ 0 := fun i =>
    ne_of_gt (stationaryVec_pos A hd i)
  simp only [chiSquareDistance, walkDensity]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hπi := hpos i
  field_simp
  ring

/-- **The plain-ℓ² corollary bridge** (the scoping record's
unweighted form): for any bound `c` on the stationary weights, the
unweighted sum of squared deviations is at most `c` times the χ²
distance. Instantiating `c` at the largest stationary weight recovers
the Euclidean `‖ν_t − π‖₂² ≤ max π · χ²(t, x)`. This is how any
consumer wanting the proposal sketch's unweighted statement obtains it
from the weighted proxy. -/
theorem sum_sub_sq_walkDistribution_le (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) (c : ℝ)
    (hc : ∀ i, stationaryVec A i ≤ c) :
    ∑ i, (walkDistribution A t x i - stationaryVec A i)^2
      ≤ c * chiSquareDistance A t x := by
  have hpos : ∀ i, stationaryVec A i ≠ 0 := fun i =>
    ne_of_gt (stationaryVec_pos A hd i)
  have hterm : ∀ i : V,
      (walkDistribution A t x i - stationaryVec A i)^2
      = stationaryVec A i * ((walkDistribution A t x i
          - stationaryVec A i)^2 / stationaryVec A i) := by
    intro i
    have hπi := hpos i
    field_simp
  rw [chiSquareDistance]
  have h1 : ∑ i, (walkDistribution A t x i - stationaryVec A i)^2
      ≤ ∑ i, c * ((walkDistribution A t x i - stationaryVec A i)^2
        / stationaryVec A i) :=
    Finset.sum_le_sum fun i _ => by
      calc (walkDistribution A t x i - stationaryVec A i)^2
          = stationaryVec A i * ((walkDistribution A t x i
              - stationaryVec A i)^2 / stationaryVec A i) := hterm i
        _ ≤ c * ((walkDistribution A t x i
              - stationaryVec A i)^2 / stationaryVec A i) :=
            mul_le_mul_of_nonneg_right (hc i)
              (div_nonneg (sq_nonneg _)
                (le_of_lt (stationaryVec_pos A hd i)))
  rw [Finset.mul_sum]
  exact h1

/-!
## The geometric decay engine (Step 3, component 1)

The matrix-power/eigencomponent layer of the Step-3 decay bound,
delivered as its own hard-crust component (the proposal's sub-decomposition
license for its hardest step). The engine conjugates walk powers to the
symmetric side (`degreeSqrt_mulVec_pow_walkTransitionMatrix`), evolves
each eigencoordinate geometrically, and resolves the π-weighted norm
through Parseval — leaving only the density-to-χ² gluing and the
connectivity kernel characterization to the second component.

Statement-shape decisions (recorded before stating): the non-decaying
mode is excluded *by value* (`eigvalOf (L_sym) i = 0`), not by spectral
index — the index form is only correct when the kernel is
one-dimensional, while the value form keeps the contraction true
unconditionally (on a disconnected graph the mode hypothesis honestly
fails for a one-component start, which is exactly right: there is no
decay to global stationarity); the rate is hypothesis-shaped `r` rather
than a packaged sup; and no sign hypothesis on `r` is carried — the
rate hypothesis already forces `r ≥ 0` whenever it is non-vacuous.
-/

/-- **Eigencoordinate evolution**: the `i`-th eigencoefficient (against
the orthonormal eigenbasis of `L_sym`) of the conjugated `t`-step walk
evolution is the initial coefficient multiplied by `(1 - μ i) ^ t`.
Composed from the conjugated-power transfer and the generic eigenaction
at `1 − M`; load-bearing on both — a wrong similarity orientation or a
wrong reflection would change the factor here. -/
theorem eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (t : ℕ) (g : V → ℝ) (i : V) :
    Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        (degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g))
      = (1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i) ^ t
        * Matrix.dotProduct
            (eigvecOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i)
            (degreeSqrt A *ᵥ g) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [degreeSqrt_mulVec_pow_walkTransitionMatrix A hd (t + 1) g,
      pow_succ', ← Matrix.mulVec_mulVec,
      eigvecOf_dotProduct_one_sub_mulVec,
      ← degreeSqrt_mulVec_pow_walkTransitionMatrix A hd t g, ih,
      pow_succ', mul_assoc]

/-- **The Parseval-exact decay identity**: the squared Euclidean norm of
the conjugated `t`-step evolution is the eigenvalue-weighted sum of
squared initial eigencoordinates, each weight `(1 - μ i) ^ (2t)`. This is
the exact quantity the χ² distance becomes in conjugated coordinates
(Step 2's `chiSquareDistance_eq_sum_smul` rescaled by `vol⁻¹`); no
inequality is lost here. -/
theorem dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (t : ℕ) (g : V → ℝ) :
    Matrix.dotProduct
        (degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g))
        (degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g))
      = ∑ i, ((1 - eigvalOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i) ^ t
          * Matrix.dotProduct
              (eigvecOf (normalizedLaplacian A)
                (normalizedLaplacian_symmetric A hA) i)
              (degreeSqrt A *ᵥ g)) ^ 2 := by
  rw [dotProduct_eigvecOf (normalizedLaplacian_symmetric A hA) _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix
      A hA hd t g i, pow_two]

/-- **The ℓ²(π) contraction, norm form**: if the conjugated initial
vector has no component on the zero-eigenvalue modes of `L_sym` (the
*mode* hypothesis — value-based, so degenerate graphs are handled
honestly), and every decaying eigenvalue's walk factor is bounded by
`r` in absolute value (the *rate* hypothesis), then the `t`-step walk
evolution contracts the conjugated norm at rate `r ^ (2t)`. No sign
hypothesis on `r`: the rate hypothesis forces `r ≥ 0` whenever it binds,
and when it is vacuous every coefficient is killed by the mode
hypothesis. -/
theorem dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix_le
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (g : V → ℝ) (r : ℝ) (t : ℕ)
    (hmode : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i = 0 →
        Matrix.dotProduct
          (eigvecOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i)
          (degreeSqrt A *ᵥ g) = 0)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
        |1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i| ≤ r) :
    Matrix.dotProduct
        (degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g))
        (degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g))
      ≤ r ^ (2 * t)
        * Matrix.dotProduct (degreeSqrt A *ᵥ g) (degreeSqrt A *ᵥ g) := by
  classical
  rw [dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix A hA hd t g]
  have hterm : ∀ i : V,
      ((1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i) ^ t
        * Matrix.dotProduct
            (eigvecOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i)
            (degreeSqrt A *ᵥ g)) ^ 2
      ≤ r ^ (2 * t) * (Matrix.dotProduct
          (eigvecOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i)
          (degreeSqrt A *ᵥ g)) ^ 2 := by
    intro i
    by_cases hμ : eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i = 0
    · rw [hmode i hμ]
      simp
    · have hr0 : 0 ≤ r :=
        le_trans (abs_nonneg _) (hrate i hμ)
      have hrt : 0 ≤ r ^ t := pow_nonneg hr0 t
      have habspow : |(1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i) ^ t|
          = |1 - eigvalOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i| ^ t :=
        abs_pow _ _
      have hle : |(1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i) ^ t| ≤ r ^ t := by
        rw [habspow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hrate i hμ) t
      have key : ((1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i) ^ t) ^ 2
          ≤ (r ^ t) ^ 2 := by
        rw [← sq_abs ((1 - eigvalOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i) ^ t)]
        refine sq_le_sq' ?_ hle
        linarith [abs_nonneg ((1 - eigvalOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i) ^ t), hrt]
      have hrw : r ^ (2 * t) = (r ^ t) ^ 2 := by
        rw [mul_comm 2 t, pow_mul]
      rw [hrw, mul_pow]
      exact mul_le_mul_of_nonneg_right key (sq_nonneg _)
  calc ∑ i, ((1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i) ^ t
        * Matrix.dotProduct
            (eigvecOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i)
            (degreeSqrt A *ᵥ g)) ^ 2
      ≤ ∑ i, r ^ (2 * t) * (Matrix.dotProduct
          (eigvecOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i)
          (degreeSqrt A *ᵥ g)) ^ 2 :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = r ^ (2 * t) * ∑ i, (Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        (degreeSqrt A *ᵥ g)) ^ 2 :=
          (Finset.mul_sum _ _ _).symm
    _ = r ^ (2 * t) * Matrix.dotProduct (degreeSqrt A *ᵥ g)
        (degreeSqrt A *ᵥ g) := by
          refine congrArg _ ?_
          rw [dotProduct_eigvecOf (normalizedLaplacian_symmetric A hA)
            (degreeSqrt A *ᵥ g) (degreeSqrt A *ᵥ g)]
          exact Finset.sum_congr rfl fun i _ => (pow_two _)

/-- **The π-norm bridge**: the π-weighted sum of squares is the squared
Euclidean norm of the `√D`-conjugate, rescaled by `vol⁻¹` — the exact
identification under which Step 2's density-form χ²
(`chiSquareDistance_eq_sum_smul`) and the conjugated-norm engine above
are the same quantity. Needs only degree nonnegativity (for the square
roots); no volume-positivity hypothesis, since both sides carry the same
`vol⁻¹` factor. -/
theorem sum_stationaryVec_smul_sq_eq (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) (f : V → ℝ) :
    ∑ i, stationaryVec A i * (f i) ^ 2
      = (vol A (Finset.univ : Finset V))⁻¹
        * Matrix.dotProduct (degreeSqrt A *ᵥ f) (degreeSqrt A *ᵥ f) := by
  have hside : ∀ i : V,
      (degreeSqrt A *ᵥ f) i * (degreeSqrt A *ᵥ f) i
        = deg A i * (f i) ^ 2 := by
    intro i
    have hd1 : (degreeSqrt A *ᵥ f) i = Real.sqrt (deg A i) * f i := by
      simp [degreeSqrt, Matrix.mulVec_diagonal]
    have hd2 : Real.sqrt (deg A i) * Real.sqrt (deg A i) = deg A i :=
      Real.mul_self_sqrt (le_of_lt (hd i))
    rw [hd1]
    calc (Real.sqrt (deg A i) * f i) * (Real.sqrt (deg A i) * f i)
        = (Real.sqrt (deg A i) * Real.sqrt (deg A i)) * (f i * f i) := by
          ring
      _ = deg A i * (f i * f i) := by rw [hd2]
      _ = deg A i * (f i) ^ 2 := by rw [sq]
  have hterm : ∀ i : V, stationaryVec A i * (f i) ^ 2
      = (vol A (Finset.univ : Finset V))⁻¹
        * (deg A i * (f i) ^ 2) := by
    intro i
    rw [stationaryVec, div_eq_inv_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  congr 1
  simp only [Matrix.dotProduct]
  exact Finset.sum_congr rfl fun i _ => (hside i).symm

/-- **The ℓ²(π) contraction** — Step 3's decay engine in mixing
coordinates: under the mode hypothesis (no component of the conjugate of
`g` on the zero-eigenvalue modes of `L_sym`) and the rate hypothesis
(`r` dominating every decaying walk factor `|1 − μ i|`), the `t`-step
walk evolution contracts the π-weighted norm of `g` by `r ^ (2t)`. The
second Step-3 component instantiates this at the centered initial
density `g = h₀ − 1` (where the mode hypothesis follows from
connectivity and mass conservation) to obtain the χ² mixing bound. -/
theorem sum_stationaryVec_smul_sq_pow_walkTransitionMatrix_le
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (g : V → ℝ) (r : ℝ) (t : ℕ)
    (hmode : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i = 0 →
        Matrix.dotProduct
          (eigvecOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i)
          (degreeSqrt A *ᵥ g) = 0)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
        |1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i| ≤ r) :
    ∑ i, stationaryVec A i * (((walkTransitionMatrix A ^ t) *ᵥ g) i) ^ 2
      ≤ r ^ (2 * t) * ∑ i, stationaryVec A i * (g i) ^ 2 := by
  have hvol : 0 ≤ vol A (Finset.univ : Finset V) :=
    Finset.sum_nonneg fun i _ => le_of_lt (hd i)
  have heng := dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix_le
    A hA hd g r t hmode hrate
  have hL := sum_stationaryVec_smul_sq_eq A hd
    fun i => ((walkTransitionMatrix A ^ t) *ᵥ g) i
  have hR := sum_stationaryVec_smul_sq_eq A hd g
  rw [hL, hR]
  calc (vol A (Finset.univ : Finset V))⁻¹
        * Matrix.dotProduct
            (degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g))
            (degreeSqrt A *ᵥ ((walkTransitionMatrix A ^ t) *ᵥ g))
      ≤ (vol A (Finset.univ : Finset V))⁻¹
          * (r ^ (2 * t)
            * Matrix.dotProduct (degreeSqrt A *ᵥ g)
              (degreeSqrt A *ᵥ g)) :=
        mul_le_mul_of_nonneg_left heng (inv_nonneg.mpr hvol)
    _ = r ^ (2 * t) * ((vol A (Finset.univ : Finset V))⁻¹
        * Matrix.dotProduct (degreeSqrt A *ᵥ g)
          (degreeSqrt A *ᵥ g)) := by ring

/-!
## The χ² assembly (Step 3, component 2) — the mixing statement

The program's closing composition: the centered density evolves by walk
powers (`walkDensity_sub_one`), connectivity pins the non-decaying modes
of the symmetrized operator to the constant direction
(`eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero`,
the shelf's `laplacian_kernel_eq_span_onesVec` transferred through the
proved congruence `√D L_sym √D = L` and composed with mass
conservation), and the delivered ℓ²(π) contraction then reads directly
as the χ² mixing bound `chiSquareDistance_le_of_connected` —
`χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)`, the proposal's target statement.

Statement-shape decisions (recorded before stating): connectivity enters
as the shelf kernel theorem's exact hypotheses
(`(supportGraph A hA).Connected` plus entrywise nonnegativity — honest,
since mixing to *global* stationarity genuinely needs it); the rate
stays hypothesis-shaped `r` (component 1's recorded decision — the
`sup'` packaging of λ* remains a consumer's business); `t = 0` needs no
special case (the bound reads `χ²(0) ≤ 1 · χ²(0)`).
-/

/-- **Centered evolution**: the centered density `h_t − 1` evolves by the
`t`-th power of the walk matrix itself — `h_t − 1 = Pᵗ *ᵥ (h₀ − 1)`. One
induction from the density evolution `walkDensity_succ` plus the
constant fix `walkTransitionMatrix_mulVec_one` (`P *ᵥ 1 = 1`, the
stationary direction that subtracting `1` removes). This is the bridge
between the mixing objects of Step 2 and the matrix-power engine of
Step 3 component 1: the centered density is exactly the vector `g` the
contraction consumes. -/
theorem walkDensity_sub_one (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    walkDensity A t x - 1
      = (walkTransitionMatrix A ^ t) *ᵥ (walkDensity A 0 x - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hP1 : walkTransitionMatrix A *ᵥ (1 : V → ℝ) = 1 :=
      walkTransitionMatrix_mulVec_one A hd
    rw [walkDensity_succ A hA hd t x, pow_succ',
      ← Matrix.mulVec_mulVec]
    calc walkTransitionMatrix A *ᵥ walkDensity A t x - 1
        = walkTransitionMatrix A *ᵥ walkDensity A t x
            - walkTransitionMatrix A *ᵥ (1 : V → ℝ) := by rw [hP1]
      _ = walkTransitionMatrix A *ᵥ (walkDensity A t x - 1) :=
            (Matrix.mulVec_sub _ _ _).symm
      _ = walkTransitionMatrix A *ᵥ
            ((walkTransitionMatrix A ^ t) *ᵥ (walkDensity A 0 x - 1)) := by
              rw [ih]

/-- **Mass conservation in the conjugated pairing**: the degree-weighted
sum of the centered initial density is zero,
`∑ k, deg A k * (h₀ k − 1) = 0` — termwise `deg · h₀ = vol · ν₀` (the
density undoes the stationary rescaling), and both sums evaluate to
`vol` (the law and the stationary vector both sum to one). This is the
orthogonality of `√D *ᵥ (h₀ − 1)` to the constant direction, before
conjugation. -/
theorem sum_deg_mul_walkDensity_sub_one_eq_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (x : V) :
    ∑ k, deg A k * (walkDensity A 0 x k - 1) = 0 := by
  have hvol : vol A (Finset.univ : Finset V) ≠ 0 :=
    ne_of_gt (vol_univ_pos A hd)
  have hterm : ∀ k : V, deg A k * (walkDensity A 0 x k - 1)
      = vol A (Finset.univ : Finset V) * walkDistribution A 0 x k
          - deg A k := by
    intro k
    have hdk : deg A k ≠ 0 := ne_of_gt (hd k)
    rw [walkDensity, stationaryVec]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_walkDistribution A hd 0 x,
    show (∑ k, deg A k) = vol A (Finset.univ : Finset V) from rfl,
    mul_one, sub_self]

/-- **The connectivity mode derivation**: on a connected graph, every
zero-eigenvalue eigenvector of the normalized Laplacian is orthogonal to
the conjugated centered initial density. This is the mode hypothesis of
the contraction, derived — not assumed: the eigenvector lies in
`ker L_sym` (the eigen equation at `μ = 0`), the kernel transfers
through the congruence `√D L_sym √D = L` to the combinatorial kernel
(the pre-conjugated vector `(1/√D) *ᵥ v` is killed by `laplacian A`),
connectivity pins that vector to a constant (`v k = √(deg k) · c`
entrywise), and the dot product collapses to
`c · ∑ deg (h₀ − 1) = 0` by mass conservation. Load-bearing on the
kernel characterization `exists_const_of_laplacian_mulVec_eq_zero`, the
congruence `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`, and the
mass conservation above — an error in any would surface here. -/
theorem eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hconn : (supportGraph A hA).Connected) (x : V) {i : V}
    (hμ : eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i = 0) :
    Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        (degreeSqrt A *ᵥ (walkDensity A 0 x - 1)) = 0 := by
  classical
  have heqb : normalizedLaplacian A *ᵥ
      (eigvecOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i)
      = eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i
        • (eigvecOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i) :=
    (isHermitian_of_isSymm
      (normalizedLaplacian_symmetric A hA)).mulVec_eigenvectorBasis i
  rw [hμ, zero_smul] at heqb
  set v := eigvecOf (normalizedLaplacian A)
    (normalizedLaplacian_symmetric A hA) i with hv
  rw [hv] at heqb
  have hev : normalizedLaplacian A *ᵥ v = 0 := heqb
  have hcancel : degreeSqrt A *ᵥ (degreeInvSqrt A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, degreeSqrt_mul_degreeInvSqrt A hd,
      Matrix.one_mulVec]
  have hkerL : laplacian A *ᵥ (degreeInvSqrt A *ᵥ v) = 0 := by
    have hcongr : ∀ u : V → ℝ, laplacian A *ᵥ u
        = degreeSqrt A *ᵥ (normalizedLaplacian A *ᵥ
            (degreeSqrt A *ᵥ u)) := by
      intro u
      rw [← degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt A hd,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hcongr, hcancel, hev, Matrix.mulVec_zero]
  obtain ⟨c, hc⟩ := exists_const_of_laplacian_mulVec_eq_zero
    A hA hnonneg hconn hkerL
  have hentry : ∀ k : V, v k = Real.sqrt (deg A k) * c := by
    intro k
    have h0 := congrFun hc k
    rw [degreeInvSqrt_mulVec_apply] at h0
    have hs : Real.sqrt (deg A k) ≠ 0 := Real.sqrt_ne_zero'.mpr (hd k)
    calc v k = Real.sqrt (deg A k)
          * ((Real.sqrt (deg A k))⁻¹ * v k) := by
            rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
      _ = Real.sqrt (deg A k) * c := by rw [h0]
  have hdot : ∀ k : V, v k * (degreeSqrt A *ᵥ (walkDensity A 0 x - 1)) k
      = c * (deg A k * (walkDensity A 0 x k - 1)) := by
    intro k
    calc v k * (degreeSqrt A *ᵥ (walkDensity A 0 x - 1)) k
        = (Real.sqrt (deg A k) * c)
            * (Real.sqrt (deg A k) * (walkDensity A 0 x k - 1)) := by
              rw [hentry k, degreeSqrt_mulVec_apply, Pi.sub_apply,
                Pi.one_apply]
      _ = (Real.sqrt (deg A k) * Real.sqrt (deg A k))
            * (c * (walkDensity A 0 x k - 1)) := by ring
      _ = deg A k * (c * (walkDensity A 0 x k - 1)) := by
              rw [Real.mul_self_sqrt (le_of_lt (hd k))]
      _ = c * (deg A k * (walkDensity A 0 x k - 1)) := by ring
  rw [Matrix.dotProduct, Finset.sum_congr rfl fun k _ => hdot k,
    ← Finset.mul_sum,
    sum_deg_mul_walkDensity_sub_one_eq_zero A hd x, mul_zero]

/-- **The χ² mixing bound** — the mixing-time program's target statement:
on a connected graph with symmetric nonnegative weights and positive
degrees, if `r` dominates every decaying walk factor
`|1 − μ|` (`μ` over the nonzero normalized-Laplacian eigenvalues), then
the χ² distance from stationarity after `t` steps is at most
`r ^ (2t) · ((π x)⁻¹ − 1)`. Composition: the density-form χ², the
centered evolution, the delivered ℓ²(π) contraction with the mode
hypothesis supplied by connectivity, and the `t = 0` normalization.
Everything is proved — zero new axioms; the only external input is the
rate hypothesis, which the consumer instantiates from the spectrum. -/
theorem chiSquareDistance_le_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hconn : (supportGraph A hA).Connected) (r : ℝ) (t : ℕ) (x : V)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r) :
    chiSquareDistance A t x
      ≤ r ^ (2 * t) * ((stationaryVec A x)⁻¹ - 1) := by
  have hmode : ∀ i : V, eigvalOf (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) i = 0 →
      Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        (degreeSqrt A *ᵥ (walkDensity A 0 x - 1)) = 0 :=
    fun i hμ =>
      eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero
        A hA hnonneg hd hconn x hμ
  have hctr := sum_stationaryVec_smul_sq_pow_walkTransitionMatrix_le
    A hA hd (walkDensity A 0 x - 1) r t hmode hrate
  have hcenter : ∀ i : V, (walkDensity A t x i - 1)
      = ((walkTransitionMatrix A ^ t) *ᵥ (walkDensity A 0 x - 1)) i := by
    intro i
    rw [← congrFun (walkDensity_sub_one A hA hd t x) i, Pi.sub_apply,
      Pi.one_apply]
  rw [chiSquareDistance_eq_sum_smul A hd t x]
  have hsum : ∑ i, stationaryVec A i * (walkDensity A t x i - 1)^2
      = ∑ i, stationaryVec A i
          * (((walkTransitionMatrix A ^ t) *ᵥ
              (walkDensity A 0 x - 1)) i)^2 :=
    Finset.sum_congr rfl fun i _ => by rw [hcenter i]
  rw [hsum]
  have h0 : ∑ i, stationaryVec A i * ((walkDensity A 0 x - 1) i)^2
      = chiSquareDistance A 0 x := by
    rw [chiSquareDistance_eq_sum_smul A hd 0 x]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Pi.sub_apply, Pi.one_apply]
  calc ∑ i, stationaryVec A i
        * (((walkTransitionMatrix A ^ t) *ᵥ
            (walkDensity A 0 x - 1)) i)^2
      ≤ r ^ (2 * t)
          * ∑ i, stationaryVec A i * ((walkDensity A 0 x - 1) i)^2 :=
            hctr
    _ = r ^ (2 * t) * chiSquareDistance A 0 x := by rw [h0]
    _ = r ^ (2 * t) * ((stationaryVec A x)⁻¹ - 1) := by
          rw [chiSquareDistance_zero A hd x]

end SpectralGraphTheory
