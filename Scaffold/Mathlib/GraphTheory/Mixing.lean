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
import Scaffold.Mathlib.GraphTheory.Heat

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
goal; the ℓ² → TV conversion was a separate further step (the
proposal's own Step 4 framing) — delivered 2026-08-31 as its own
proposal, in the module's `TotalVariation` section below. Within ℓ²,
the *weighted* form is
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
- the **total-variation distance and the ℓ² conversion** (the mixing
  program's deferred Step 4, delivered 2026-08-31 as its own proposal
  `proposals/total-variation-mixing-conversion.md`): `tvDistance` in
  its finite-state vector form `(1/2) ∑ i, |μ i − ν i|` — the scoping
  decision recorded in that proposal dissolves the original Step-4
  cost estimate (no `MeasureTheory` wrapper: the module is already
  vector-valued, and for probability vectors this `L¹` form *is* the
  classical finite-state TV) — with symmetry, the triangle
  inequality, the generic Cauchy–Schwarz conversion
  `tvDistance_le_half_sqrt` (`TV ≤ (1/2)·√χ²` at the sharp classical
  constant, attained exactly on `K₂`), the unconditional walk-level
  shadow `walkDistribution_tvDistance_le`, and the rate form
  `walkDistribution_tvDistance_le_of_connected` — the closing χ² bound
  restated in the field-standard mixing distance. (The depth-form TV
  ceiling and its two-start twin live in `Oversmoothing.lean`, beside
  the entrywise family they twin.)

Everything here is proved; no axiom is admitted. The pinned Mathlib
has no chi-square, total-variation, or mixing-time objects (surveyed
2026-08-22; `docs/8_MATHLIB_COVERAGE_MAP.md` records the upstream
absence), so this module is original Scaffold surface.

The Poisson-bridge section (2026-09-01, the same proposal's named
follow-on) adds the Poissonization identity
`contWalkDistribution_eq_tsum_walkDistribution` (the continuous walk
law as the Poisson mixture of the discrete laws — LPW ch. 20's `H_t`
at the law level, this module's first tsum construction), the TV
contraction toolkit (`Pᵀ` ℓ¹-contraction, discrete TV monotonicity),
the comparability `contWalkDistribution_tvDistance_add_le`, and the
discrete-certificate transfer corollary.
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
## Nonnegativity of the walk law
-/

/-- Entrywise nonnegativity of the general walk transition matrix at
nonnegative weights and positive degrees: `P i j = (deg A i)⁻¹ A i j
≥ 0`. Support lemma for the walk law's nonnegativity, the hypothesis
that makes `walkDistribution` a legal factor distribution for
`Probability.IIDProduct.iidPMF`. -/
theorem walkTransitionMatrix_nonneg (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (i j : V) :
    0 ≤ walkTransitionMatrix A i j := by
  rw [walkTransitionMatrix_apply]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (hd i))) (hnn i j)

/-- The walk law is entrywise nonnegative at every time: with
nonnegative weights and positive degrees, `(Pᵀ)ᵗ *ᵥ δₓ` never goes
negative — alongside `sum_walkDistribution`, this is what makes the
fixed-time walk law a probability vector and the empirical
concentration program's sampling factor
(`Scaffold.Derived.EmpiricalStationary`). -/
theorem walkDistribution_nonneg (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (t : ℕ) (x i : V) :
    0 ≤ walkDistribution A t x i := by
  have hall : ∀ j, 0 ≤ walkDistribution A t x j := by
    induction t with
    | zero =>
      intro j
      rw [walkDistribution_zero]
      by_cases h : j = x <;> simp [Pi.single_apply, h]
    | succ t ih =>
      intro j
      rw [walkDistribution_succ]
      simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply]
      exact Finset.sum_nonneg fun k _ =>
        mul_nonneg (walkTransitionMatrix_nonneg A hnn hd k j) (ih k)
  exact hall i

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

/-! ### The total-variation distance and the ℓ² conversion

The mixing program's deferred Step 4
(`proposals/total-variation-mixing-conversion.md`, delivered
2026-08-31): the field-standard mixing distance, obtained from the χ²
distance by the classical Cauchy–Schwarz step at its sharp constant
`TV ≤ (1/2)·√χ²` — no `MeasureTheory` anywhere (the scoping decision
that dissolved the original Step-4 cost estimate). -/

/-- The total-variation distance between two vectors on the finite
vertex type, in its finite-state vector form
`tvDistance μ ν = (1/2) ∑ i, |μ i − ν i|`. Scoping record (the mixing
program's own Step-4 idiom): no `MeasureTheory` anywhere — this
module is vector-valued, and for probability vectors this `L¹` form
*is* the classical finite-state total variation (equal to the
max-over-events discrepancy `sup_A |μ A − ν A|`, a fact we do not
need and do not restate). Real arithmetic throughout —
`noncomputable` like the module's other distances. -/
noncomputable def tvDistance (μ ν : V → ℝ) : ℝ :=
  (1/2) * ∑ i, |μ i - ν i|

omit [DecidableEq V] in
theorem tvDistance_nonneg (μ ν : V → ℝ) : 0 ≤ tvDistance μ ν := by
  rw [tvDistance]
  positivity

omit [DecidableEq V] in
theorem tvDistance_symm (μ ν : V → ℝ) :
    tvDistance μ ν = tvDistance ν μ := by
  simp only [tvDistance, abs_sub_comm]

omit [DecidableEq V] in
/-- The triangle inequality — the only structural fact the two-start
corollary needs. -/
theorem tvDistance_triangle (μ ν ρ : V → ℝ) :
    tvDistance μ ρ ≤ tvDistance μ ν + tvDistance ν ρ := by
  have hpt : ∀ i : V, |μ i - ρ i| ≤ |μ i - ν i| + |ν i - ρ i| := by
    intro i
    rw [← sub_add_sub_cancel]
    exact abs_add _ _
  have hsum : ∑ i, |μ i - ρ i|
      ≤ ∑ i, (|μ i - ν i| + |ν i - ρ i|) :=
    Finset.sum_le_sum fun i _ => hpt i
  rw [Finset.sum_add_distrib] at hsum
  simp only [tvDistance]
  linarith

omit [DecidableEq V] in
/-- **The ℓ² → total-variation conversion** — the classical
Cauchy–Schwarz step, at its sharp constant: for a positive weight `w`
of total mass one and any vector `ν`, the total-variation distance
from `ν` to `w` is at most half the square root of the χ² distance
`∑ i, (ν i − w i)² / w i`. Both remaining hypotheses are load-bearing:
a mass-`2` weight refutes the un-guarded form
(`tv_conversion_mass_guard_refuted_QA`), while the `|ν i − w i| =
w i · |ν i / w i − 1|` identity is sign-free — no sign or mass
hypothesis on `ν` is needed, the bound holding for arbitrary signed
vectors, not just probability vectors. -/
theorem tvDistance_le_half_sqrt {w ν : V → ℝ} (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1) :
    tvDistance ν w
      ≤ (1/2) * Real.sqrt (∑ i, (ν i - w i)^2 / w i) := by
  have hpt : ∀ i : V, |ν i - w i| = w i * |ν i / w i - 1| := by
    intro i
    have hwi : w i ≠ 0 := ne_of_gt (hw i)
    have hkey : ν i - w i = w i * (ν i / w i - 1) := by
      field_simp
    rw [hkey, abs_mul, abs_of_pos (hw i)]
  have hTV : 2 * tvDistance ν w
      = ∑ i, w i * |ν i / w i - 1| := by
    have h2 : (2 : ℝ) * tvDistance ν w = ∑ i, |ν i - w i| := by
      rw [tvDistance, ← mul_assoc,
        show (2 : ℝ) * (1/2) = 1 from by norm_num, one_mul]
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => hpt i
  have hcs : (∑ i, w i * |ν i / w i - 1|)^2
      ≤ (∑ i, w i) * ∑ i, w i * (ν i / w i - 1)^2 := by
    have hgen := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V)
      (fun i => Real.sqrt (w i))
      (fun i => Real.sqrt (w i) * |ν i / w i - 1|)
    have hfg : ∀ i : V, (Real.sqrt (w i))
        * (Real.sqrt (w i) * |ν i / w i - 1|)
        = w i * |ν i / w i - 1| := by
      intro i
      rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt (hw i))]
    have hfsq : ∀ i : V, (Real.sqrt (w i))^2 = w i :=
      fun i => Real.sq_sqrt (le_of_lt (hw i))
    have hgsq : ∀ i : V, (Real.sqrt (w i) * |ν i / w i - 1|)^2
        = w i * (ν i / w i - 1)^2 := by
      intro i
      rw [mul_pow, hfsq i, sq_abs]
    rw [Finset.sum_congr rfl fun i _ => hfg i,
      Finset.sum_congr rfl fun i _ => hfsq i,
      Finset.sum_congr rfl fun i _ => hgsq i] at hgen
    exact hgen
  have hsum2 : ∑ i, w i * (ν i / w i - 1)^2
      = ∑ i, (ν i - w i)^2 / w i :=
    Finset.sum_congr rfl fun i _ => by
      have hwi : w i ≠ 0 := ne_of_gt (hw i)
      field_simp
      ring
  rw [hw1, one_mul, hsum2] at hcs
  have key : (2 * tvDistance ν w)^2
      ≤ ∑ i, (ν i - w i)^2 / w i := by
    rw [hTV]
    exact hcs
  have htvnn : 0 ≤ 2 * tvDistance ν w := by
    rw [tvDistance]
    positivity
  have hkey2 : Real.sqrt ((2 * tvDistance ν w)^2)
      ≤ Real.sqrt (∑ i, (ν i - w i)^2 / w i) :=
    Real.sqrt_le_sqrt key
  rw [Real.sqrt_sq htvnn] at hkey2
  linarith

/-- **The walk-level conversion**: the χ² mixing bound's TV shadow —
the walk law's total-variation distance to stationarity is at most
half the square root of the χ² distance, unconditionally (no
connectivity, no rate: every hypothesis here is one this module
already proves for every walk). -/
theorem walkDistribution_tvDistance_le (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    tvDistance (walkDistribution A t x) (stationaryVec A)
      ≤ (1/2) * Real.sqrt (chiSquareDistance A t x) :=
  tvDistance_le_half_sqrt (stationaryVec_pos A hd)
    (sum_stationaryVec A hd)

/-- **The rate form** — the mixing program's closing bound restated in
total variation: under exactly `chiSquareDistance_le_of_connected`'s
hypothesis set, `TV(ν_t x, π) ≤ (1/2) · √(r^{2t} · ((π x)⁻¹ − 1))`.
Pure hard crust: one Cauchy–Schwarz step composed with the proved χ²
bound. QA: the exact-attainment pin `k2_conversion_attained_QA` (on
`K₂` at `t = 1`, `TV = (1/2)·√χ²` with both sides `1/2` — the
constant sharp) and the triangle instances at `t = 1, 2, 3`
(`tri_tv_*_eq_QA`), with the depth-form consumers' QA in
`Mixing_QA.lean`'s TV section. -/
theorem walkDistribution_tvDistance_le_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hconn : (supportGraph A hA).Connected) (r : ℝ)
    (t : ℕ) (x : V)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r) :
    tvDistance (walkDistribution A t x) (stationaryVec A)
      ≤ (1/2) * Real.sqrt
          (r ^ (2 * t) * ((stationaryVec A x)⁻¹ - 1)) := by
  refine (walkDistribution_tvDistance_le A hd t x).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt
      (chiSquareDistance_le_of_connected A hA hnn hd hconn r t x hrate))
    (by norm_num)

/-!
## Continuous time

`proposals/continuous-time-chi-square-mixing.md` (2026-08-31): the
continuous-time walk's π-density `contWalkDensity` (the walk density
under `e^{-tL_walk}`), the centered-density conjugation shift
`degreeSqrt_mulVec_contWalkDensity_sub_one` (the identity every exact
computation runs through), the continuous χ² distance
`contChiSquareDistance` with its `t = 0` join to the discrete object,
and the consumer `contChiSquareDistance_le` — the field-standard
continuous-time mixing bound at the discrete theorem's hypothesis set
*minus connectivity* (at `λ₂(L_sym) = 0` the true rate-1 statement) and
with *no caller-certified rate*: the continuous rate `e^{-λ₂ t}` is
intrinsic. All proved, zero axioms.

The mixing-time package (2026-08-31, the same proposal's deferred
items 1+2): the continuous walk *law* `contWalkDistribution` with its
`t = 0` join, the ℓ²→TV conversion's continuous twins
`contWalkDistribution_tvDistance_le` / `_of_decay`, the mixing-time
object `contMixingTimeFrom` (the per-start `sInf` at Levin–Peres–Wilmer
ch. 20's `∀ s ≥ t` reading), its certificate interface
`_le_of_cert`, the spectral ceiling `_le_of_connected`, and
ε-antitonicity `_anti`. All proved, zero axioms.
-/

/-- Degree-weighted sums are preserved by the walk heat semigroup on
symmetric input: `∑ deg·(e^{−tL_walk} f) = ∑ deg·f` — mass conservation
in π-coordinates (the twin of `sum_heatKernel_mulVec`). Route: the
π-isometry moves the sum to the `√D·1` pairing, the conjugation moves
it to the normalized kernel, symmetry moves `√D·1` across, and the
kernel fix returns it. -/
theorem sum_deg_mul_walkHeatKernel (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) (t : ℝ) (f : V → ℝ) :
    ∑ i, deg A i * (walkHeatKernel A t *ᵥ f) i = ∑ j, deg A j * f j := by
  have he : ∀ i : V, (degreeSqrt A *ᵥ onesVec : V → ℝ) i
      * (degreeSqrt A *ᵥ (walkHeatKernel A t *ᵥ f) : V → ℝ) i
      = deg A i * (walkHeatKernel A t *ᵥ f) i := by
    intro i
    rw [degreeSqrt_mulVec_apply, degreeSqrt_mulVec_apply]
    simp only [onesVec, mul_one]
    rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt (hd i))]
  calc ∑ i, deg A i * (walkHeatKernel A t *ᵥ f) i
      = Matrix.dotProduct (degreeSqrt A *ᵥ onesVec)
          (degreeSqrt A *ᵥ (walkHeatKernel A t *ᵥ f)) := by
        rw [Matrix.dotProduct]
        exact Finset.sum_congr rfl fun i _ => (he i).symm
    _ = ∑ j, deg A j * f j := by
        rw [degreeSqrt_mulVec_walkHeatKernel A hd t f,
          Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
          (normalizedHeatKernel_isSymm A hA t).eq,
          normalizedHeatKernel_mulVec_degreeSqrt_onesVec A hd t,
          ← sum_deg_mul_eq A hd f]

/-- The continuous-time walk's π-density started at `x`: the discrete
walk's initial density evolved by the walk heat semigroup
`e^{−tL_walk}` — the density process of the continuous-time random
walk (each vertex jumping at unit rate to a uniform neighbor). -/
noncomputable def contWalkDensity (A : WAdj (V := V)) (t : ℝ) (x : V) :
    V → ℝ :=
  walkHeatKernel A t *ᵥ walkDensity A 0 x

theorem contWalkDensity_zero (A : WAdj (V := V)) (x : V) :
    contWalkDensity A 0 x = walkDensity A 0 x := by
  rw [contWalkDensity, walkHeatKernel_zero, Matrix.one_mulVec]

theorem walkHeatKernel_mulVec_one (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) (t : ℝ) :
    walkHeatKernel A t *ᵥ (1 : V → ℝ) = 1 :=
  walkHeatKernel_mulVec_onesVec A hd t

/-- **The centered-density conjugation shift**: the `√D`-conjugate of
the centered continuous-time density evolves by the *normalized* heat
kernel — `√D (h_t − 1) = e^{−tL_sym} (√D (h₀ − 1))`. The identity the
consumer proof and every QA exact closed form runs through: it makes
the π-weighted χ² exactly the Euclidean contraction of the normalized
kernel on the conjugated centered initial density. -/
theorem degreeSqrt_mulVec_contWalkDensity_sub_one (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) (t : ℝ) (x : V) :
    degreeSqrt A *ᵥ (contWalkDensity A t x - 1)
      = normalizedHeatKernel A t *ᵥ
          (degreeSqrt A *ᵥ (walkDensity A 0 x - 1)) := by
  have hstep : walkHeatKernel A t *ᵥ (walkDensity A 0 x - 1)
      = contWalkDensity A t x - 1 := by
    rw [contWalkDensity, Matrix.mulVec_sub,
      walkHeatKernel_mulVec_one A hd t]
  calc degreeSqrt A *ᵥ (contWalkDensity A t x - 1)
      = degreeSqrt A *ᵥ
          (walkHeatKernel A t *ᵥ (walkDensity A 0 x - 1)) := by
        rw [hstep]
    _ = normalizedHeatKernel A t *ᵥ
          (degreeSqrt A *ᵥ (walkDensity A 0 x - 1)) :=
        degreeSqrt_mulVec_walkHeatKernel A hd t _

/-- The continuous-time walk density stays a density: `∑ π h_t = 1`
at every time. -/
theorem sum_stationaryVec_contWalkDensity (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℝ)
    (x : V) :
    ∑ i, stationaryVec A i * contWalkDensity A t x i = 1 := by
  have h0 : ∑ i, stationaryVec A i * walkDensity A 0 x i = 1 := by
    rw [← sum_walkDistribution A hd 0 x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [walkDensity, mul_div_cancel₀ _ (ne_of_gt (stationaryVec_pos A hd i))]
  have hconv : ∀ g : V → ℝ, ∑ i, stationaryVec A i * g i
      = (vol A (Finset.univ : Finset V))⁻¹ * ∑ i, deg A i * g i := by
    intro g
    have h1 : ∀ i : V, stationaryVec A i * g i
        = deg A i * g i / vol A (Finset.univ : Finset V) := by
      intro i
      simp only [stationaryVec, div_mul_eq_mul_div]
    have hsum : ∑ i, stationaryVec A i * g i
        = ∑ i, deg A i * g i / vol A (Finset.univ : Finset V) :=
      Finset.sum_congr rfl fun i _ => h1 i
    rw [hsum, ← Finset.sum_div, div_eq_inv_mul]
  rw [contWalkDensity, hconv, sum_deg_mul_walkHeatKernel A hA hd t,
    ← hconv, h0]

/-- The continuous-time χ² mixing distance:
`χ²_cont(t, x) = ∑ i, π i (h_t i − 1)²` — the same object as
`chiSquareDistance` at real times, in the density form
`chiSquareDistance_eq_sum_smul` already uses. -/
noncomputable def contChiSquareDistance (A : WAdj (V := V)) (t : ℝ)
    (x : V) : ℝ :=
  ∑ i, stationaryVec A i * (contWalkDensity A t x i - 1) ^ 2

theorem contChiSquareDistance_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (x : V) :
    contChiSquareDistance A 0 x = (stationaryVec A x)⁻¹ - 1 := by
  have hdef : contChiSquareDistance A 0 x
      = ∑ i, stationaryVec A i * (contWalkDensity A 0 x i - 1) ^ 2 := rfl
  rw [hdef, contWalkDensity_zero A x,
    ← chiSquareDistance_eq_sum_smul A hd 0 x, chiSquareDistance_zero A hd x]

/-- The χ² distance in conjugated-norm form: `vol · χ²_cont(t, x)` is
the squared Euclidean norm of the normalized heat kernel applied to the
conjugated centered initial density — the form every exact QA
computation evaluates. -/
theorem contChiSquareDistance_eq_inv_mul (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℝ) (x : V) :
    contChiSquareDistance A t x
      = (vol A (Finset.univ : Finset V))⁻¹
          * Matrix.dotProduct
              (degreeSqrt A *ᵥ (contWalkDensity A t x - 1))
              (degreeSqrt A *ᵥ (contWalkDensity A t x - 1)) := by
  have hconv : ∀ g : V → ℝ, ∑ i, stationaryVec A i * (g i - 1) ^ 2
      = (vol A (Finset.univ : Finset V))⁻¹
          * ∑ i, deg A i * (g i - 1) ^ 2 := by
    intro g
    have h1 : ∀ i : V, stationaryVec A i * (g i - 1) ^ 2
        = deg A i * (g i - 1) ^ 2 / vol A (Finset.univ : Finset V) := by
      intro i
      simp only [stationaryVec, div_mul_eq_mul_div]
    have hsum : ∑ i, stationaryVec A i * (g i - 1) ^ 2
        = ∑ i, deg A i * (g i - 1) ^ 2 / vol A (Finset.univ : Finset V) :=
      Finset.sum_congr rfl fun i _ => h1 i
    rw [hsum, ← Finset.sum_div, div_eq_inv_mul]
  rw [contChiSquareDistance, hconv (contWalkDensity A t x),
    ← sum_deg_mul_sq_eq A hd (contWalkDensity A t x - 1)]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.sub_apply, Pi.one_apply, pow_two]

/-- **The continuous-time χ² mixing bound** — the field-standard
statement the twin serves, at the discrete theorem's hypothesis set
*minus connectivity* (the twin is hypothesis-minimal; on disconnected
input `λ₂(L_sym) = 0` and the bound is the true rate-1 statement) and
with **no caller-certified rate**: the continuous-time rate
`e^{−λ₂(L_sym)·t}` is intrinsic, where the discrete theorem needs an
`r` dominating every walk factor `|1 − μ|`.

`χ²_cont(t, x) ≤ e^{−2t·λ₂(L_sym)} · ((π x)⁻¹ − 1)`

Composition: the twin at the initial density (its π-mean is `1` by
mass conservation), the π↔degree conversion, and the `t = 0`
normalization joined to the discrete object. -/
theorem contChiSquareDistance_le (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) {t : ℝ} (ht : 0 ≤ t) (x : V) :
    contChiSquareDistance A t x
      ≤ Real.exp (-(2 * t * secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard))
        * ((stationaryVec A x)⁻¹ - 1) := by
  obtain ⟨v0⟩ : Nonempty V := ‹Nonempty V›
  have hsumdeg : (0 : ℝ) < ∑ j, deg A j :=
    Finset.sum_pos' (fun j _ => le_of_lt (hd j)) ⟨v0, Finset.mem_univ _, hd v0⟩
  have hmass : (∑ j, deg A j * walkDensity A 0 x j) / (∑ j, deg A j) = 1 := by
    have h1 : ∑ j, deg A j * (walkDensity A 0 x j - 1) = 0 :=
      sum_deg_mul_walkDensity_sub_one_eq_zero A hd x
    have hsplit : ∑ j, deg A j * walkDensity A 0 x j
        = (∑ j, deg A j * walkDensity A 0 x j)
          - ∑ j, deg A j * (walkDensity A 0 x j - 1) := by
      rw [h1, sub_zero]
    have h2 : ∑ j, deg A j * (walkDensity A 0 x j - 1)
        = (∑ j, deg A j * walkDensity A 0 x j) - (∑ j, deg A j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_sub, mul_one]
    rw [h2, sub_sub_cancel] at hsplit
    rw [hsplit, div_self (ne_of_gt hsumdeg)]
  have htw := walkHeatKernel_variance_decay A hA hnn hd hcard ht
    (walkDensity A 0 x)
  rw [hmass] at htw
  have hconv : ∀ g : V → ℝ, ∑ i, stationaryVec A i * (g i - 1) ^ 2
      = (vol A (Finset.univ : Finset V))⁻¹
          * ∑ i, deg A i * (g i - 1) ^ 2 := by
    intro g
    have h1 : ∀ i : V, stationaryVec A i * (g i - 1) ^ 2
        = deg A i * (g i - 1) ^ 2 / vol A (Finset.univ : Finset V) := by
      intro i
      simp only [stationaryVec, div_mul_eq_mul_div]
    have hsum : ∑ i, stationaryVec A i * (g i - 1) ^ 2
        = ∑ i, deg A i * (g i - 1) ^ 2 / vol A (Finset.univ : Finset V) :=
      Finset.sum_congr rfl fun i _ => h1 i
    rw [hsum, ← Finset.sum_div, div_eq_inv_mul]
  have h0' : (vol A (Finset.univ : Finset V))⁻¹
      * ∑ i, deg A i * (walkDensity A 0 x i - 1) ^ 2
      = (stationaryVec A x)⁻¹ - 1 := by
    rw [← hconv (walkDensity A 0 x)]
    have hdef : contChiSquareDistance A 0 x
        = ∑ i, stationaryVec A i * (contWalkDensity A 0 x i - 1) ^ 2 := rfl
    rw [contWalkDensity_zero A x] at hdef
    rw [← hdef, contChiSquareDistance_zero A hd x]
  calc contChiSquareDistance A t x
      = (vol A (Finset.univ : Finset V))⁻¹
          * ∑ i, deg A i * (contWalkDensity A t x i - 1) ^ 2 := by
        rw [contChiSquareDistance, hconv (contWalkDensity A t x)]
    _ = (vol A (Finset.univ : Finset V))⁻¹
          * ∑ i, deg A i
              * ((walkHeatKernel A t *ᵥ walkDensity A 0 x) i - 1) ^ 2 := by
        rw [contWalkDensity]
    _ ≤ (vol A (Finset.univ : Finset V))⁻¹
          * (Real.exp (-(2 * t * secondEval (normalizedLaplacian A)
                (normalizedLaplacian_symmetric A hA) hcard))
            * ∑ i, deg A i * (walkDensity A 0 x i - 1) ^ 2) := by
        exact mul_le_mul_of_nonneg_left htw (by positivity)
    _ = Real.exp (-(2 * t * secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard))
        * ((stationaryVec A x)⁻¹ - 1) := by
        rw [mul_left_comm, h0']

/-- The continuous-time walk **law** at time `t` started at `x`: the
stationary weighting of the π-density — `ν_t(i) = π i · h_t(i)`, the
actual probability vector of the walk run in continuous time. The
discrete programme's `walkDistribution` twin: there the law is
primitive and the density derived; here the semigroup evolves the
density (`contWalkDensity`), so the law is the weighting. -/
noncomputable def contWalkDistribution (A : WAdj (V := V)) (t : ℝ) (x : V) :
    V → ℝ :=
  fun i => stationaryVec A i * contWalkDensity A t x i

/-- The `t = 0` join to the discrete object: weighting the initial
density returns the point mass `δ_x`. A wrong sign or weight in
`contWalkDistribution` breaks exactly this identity. QA:
`tri_contWalkDistribution_zero_QA`. -/
theorem contWalkDistribution_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (x : V) :
    contWalkDistribution A 0 x = walkDistribution A 0 x := by
  funext i
  have hpos : stationaryVec A i ≠ 0 := ne_of_gt (stationaryVec_pos A hd i)
  show stationaryVec A i * contWalkDensity A 0 x i
      = walkDistribution A 0 x i
  rw [contWalkDensity_zero A x]
  show stationaryVec A i * (walkDistribution A 0 x i / stationaryVec A i)
      = walkDistribution A 0 x i
  field_simp

/-- The continuous χ² in the `(ν − π)²/π` form the generic ℓ²→TV
conversion consumes — the continuous twin of `chiSquareDistance`'s own
defining shape, bridged from `contChiSquareDistance`'s density form
(per-summand `π i (h i − 1)² = (π i h i − π i)²/π i`). -/
theorem contChiSquareDistance_eq_sum_div (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℝ) (x : V) :
    contChiSquareDistance A t x
      = ∑ i, (contWalkDistribution A t x i - stationaryVec A i)^2
          / stationaryVec A i := by
  rw [contChiSquareDistance]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : stationaryVec A i ≠ 0 := ne_of_gt (stationaryVec_pos A hd i)
  show stationaryVec A i * (contWalkDensity A t x i - 1)^2
      = (stationaryVec A i * contWalkDensity A t x i - stationaryVec A i)^2
          / stationaryVec A i
  field_simp
  ring

/-- **The continuous-time ℓ²→TV conversion**: the walk law's
total-variation distance to stationarity is at most half the square
root of the continuous χ² — the one-step composition of the delivered
`tvDistance_le_half_sqrt` with the delivered `contChiSquareDistance`
through the sum-div bridge. Unconditional: no connectivity, no rate,
sign-free on the law (the conversion's own shape). QA: the exact value
`k2_cont_tv_eq` (attained at every time on `K₂`) and the triangle
instances `tri_cont_tv_le` / `tri_cont_tv_slack_QA`. -/
theorem contWalkDistribution_tvDistance_le (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℝ) (x : V) :
    tvDistance (contWalkDistribution A t x) (stationaryVec A)
      ≤ (1/2) * Real.sqrt (contChiSquareDistance A t x) :=
  (tvDistance_le_half_sqrt (stationaryVec_pos A hd)
    (sum_stationaryVec A hd)).trans
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt
        (le_of_eq (contChiSquareDistance_eq_sum_div A hd t x).symm))
      (by norm_num))

/-- **The decay form** — the continuous-time TV ceiling at exactly
`contChiSquareDistance_le`'s hypothesis set (no connectivity, no
caller-certified rate: the continuous rate is intrinsic):
`TV(ν_t x, π) ≤ (1/2)·e^{−t·λ₂(L_sym)}·√((π x)⁻¹ − 1)`. QA: attained
at every time on `K₂` (`k2_cont_ceiling_attained_QA`); honest
Cauchy–Schwarz slack on the triangle (`tri_cont_tv_slack_QA`). -/
theorem contWalkDistribution_tvDistance_le_of_decay (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hcard : 2 ≤ Fintype.card V) {t : ℝ} (ht : 0 ≤ t)
    (x : V) :
    tvDistance (contWalkDistribution A t x) (stationaryVec A)
      ≤ (1/2) * Real.exp (-(t * secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard))
        * Real.sqrt ((stationaryVec A x)⁻¹ - 1) := by
  set l : ℝ := secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard with hl
  set C : ℝ := (stationaryVec A x)⁻¹ - 1 with hC
  have hχ := contChiSquareDistance_le A hA hnn hd hcard ht x
  have hTV := contWalkDistribution_tvDistance_le A hd t x
  have hsplit : Real.exp (-(2 * t * l))
      = Real.exp (-(t * l)) * Real.exp (-(t * l)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hinner : Real.sqrt (contChiSquareDistance A t x)
      ≤ Real.exp (-(t * l)) * Real.sqrt C := by
    have hnn2 : (0 : ℝ) ≤ Real.exp (-(t * l)) := Real.exp_nonneg _
    refine (Real.sqrt_le_sqrt hχ).trans_eq ?_
    rw [hsplit, Real.sqrt_mul (mul_nonneg hnn2 hnn2),
      Real.sqrt_mul_self hnn2]
  refine hTV.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hinner (by norm_num)

/-- The **continuous-time mixing time** from `x` at threshold `ε`:
the least time from which the walk law stays within `ε` of
stationarity in total variation — exactly Levin–Peres–Wilmer ch. 20's
`t_mix` reading (`inf{t : d(s) ≤ ε ∀ s ≥ t}`, the honest form for a
distance not assumed monotone in time). Per-start, mirroring the
repo's per-start oversmoothing family; the sup-over-starts uniform
object is a trivial composition left consumer-gated. Junk corner: at
an unreachable `ε` the time set is empty and `sInf ∅ = 0` in `ℝ` — no
theorem below instantiates there (every statement either carries the
connected ceiling's hypotheses, which make the set nonempty, or
hypothesizes a witness). QA: the exact closed form
`k2_contMixingTimeFrom_eq`. -/
noncomputable def contMixingTimeFrom (A : WAdj (V := V)) (x : V) (ε : ℝ) :
    ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ s : ℝ, t ≤ s →
    tvDistance (contWalkDistribution A s x) (stationaryVec A) ≤ ε}

/-- The witness-time set is bounded below by `0` by construction. -/
theorem contMixingTimeFrom_bddBelow (A : WAdj (V := V)) (x : V) (ε : ℝ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ ∀ s : ℝ, t ≤ s →
      tvDistance (contWalkDistribution A s x) (stationaryVec A) ≤ ε} :=
  ⟨0, fun _ ha => ha.1⟩

/-- Any witness time certifies the mixing time: `0 ≤ T` and
`∀ s ≥ T, TV ≤ ε` give `t_mix(ε) ≤ T` — the reusable certificate
interface (the discrete ceiling's `pow_mul_le_of_log_threshold`
analogue). -/
theorem contMixingTimeFrom_le_of_cert (A : WAdj (V := V)) (x : V)
    {ε T : ℝ} (hT0 : 0 ≤ T)
    (hT : ∀ s : ℝ, T ≤ s →
      tvDistance (contWalkDistribution A s x) (stationaryVec A) ≤ ε) :
    contMixingTimeFrom A x ε ≤ T :=
  csInf_le (contMixingTimeFrom_bddBelow A x ε) ⟨hT0, hT⟩

/-- **The spectral ceiling** — the field-standard continuous-time
mixing bound (Montenegro–Tetali's framework; LPW ch. 20's
continuous-time reading): on a connected graph,
`t_mix(ε) ≤ max 0 (ln(√((π x)⁻¹ − 1)/(2ε))/λ₂(L_sym))`. The `max 0`
floor is the honest two-case shape: past `ε = √C/2` the bound goes
negative while `t = 0` already certifies (the TV ceiling starts at
`(1/2)√C`). QA: the ceiling attained exactly on `K₂` at `ε = e^{−2}/2`
(`k2_contMixingTimeFrom_ceiling_le` beside the exact closed form
`k2_contMixingTimeFrom_exp_eq`), and the wrong-gap fence
`k2_contMixingTime_wrong_gap_refuted_QA`. -/
theorem contMixingTimeFrom_le_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) {ε : ℝ} (hε : 0 < ε)
    (x : V) :
    contMixingTimeFrom A x ε
      ≤ max 0 (Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / (2 * ε))
        / secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard) := by
  have hpos : 0 < secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard :=
    secondEval_normalizedLaplacian_pos_of_connected A hA hnn hd hcard hconn
  set C : ℝ := (stationaryVec A x)⁻¹ - 1 with hC
  set l : ℝ := secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard with hl
  rcases le_or_lt (2 * ε) (Real.sqrt C) with hle | hlt
  · have h2ε : 0 < 2 * ε := by positivity
    have hsqrt : 0 < Real.sqrt C := lt_of_lt_of_le h2ε hle
    have hratio : (1 : ℝ) ≤ Real.sqrt C / (2 * ε) :=
      (one_le_div h2ε).mpr hle
    set T : ℝ := Real.log (Real.sqrt C / (2 * ε)) / l with hTdef
    have hT0 : 0 ≤ T := div_nonneg (Real.log_nonneg hratio) (le_of_lt hpos)
    refine (contMixingTimeFrom_le_of_cert A x hT0 ?_).trans (le_max_right 0 T)
    intro s hs
    have hs0 : 0 ≤ s := le_trans hT0 hs
    have hTV := contWalkDistribution_tvDistance_le_of_decay A hA hnn hd
      hcard hs0 x
    have hsl : T * l ≤ s * l := mul_le_mul_of_nonneg_right hs (le_of_lt hpos)
    have hmono : Real.exp (-(s * l)) ≤ Real.exp (-(T * l)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hTl : T * l = Real.log (Real.sqrt C / (2 * ε)) := by
      rw [hTdef]
      field_simp
    have hbound : (1/2) * Real.exp (-(T * l)) * Real.sqrt C = ε := by
      rw [hTl, Real.exp_neg, Real.exp_log (div_pos hsqrt h2ε)]
      field_simp
    calc tvDistance (contWalkDistribution A s x) (stationaryVec A)
        ≤ (1/2) * Real.exp (-(s * l)) * Real.sqrt C := hTV
      _ ≤ (1/2) * Real.exp (-(T * l)) * Real.sqrt C := by
          nlinarith [hmono, Real.sqrt_nonneg C]
      _ = ε := hbound
  · refine (contMixingTimeFrom_le_of_cert A x (le_refl 0) ?_).trans
      (le_trans (le_refl 0) (le_max_left _ _))
    intro s hs
    have hTV := contWalkDistribution_tvDistance_le_of_decay A hA hnn hd
      hcard hs x
    have hone : Real.exp (-(s * l)) ≤ 1 := by
      have h0le : -(s * l) ≤ (0 : ℝ) := by nlinarith [hpos]
      have h := (Real.exp_le_exp.mpr h0le :
        Real.exp (-(s * l)) ≤ Real.exp (0 : ℝ))
      rwa [Real.exp_zero] at h
    calc tvDistance (contWalkDistribution A s x) (stationaryVec A)
        ≤ (1/2) * Real.exp (-(s * l)) * Real.sqrt C := hTV
      _ ≤ (1/2) * 1 * Real.sqrt C := by nlinarith [Real.sqrt_nonneg C, hone]
      _ ≤ ε := by nlinarith [hlt, Real.sqrt_nonneg C]

/-- **ε-antitonicity**: a stricter threshold takes at least as long —
`t_mix(δ) ≤ t_mix(ε)` whenever `ε ≤ δ` and `ε` is reachable from `x`
(the witness hypothesis the connected ceiling always discharges).
Field-standard monotonicity of the mixing time in its threshold. QA:
`k2_contMixingTimeFrom_anti_QA` with the closed-form consistency pin
`k2_contMixingTimeFrom_values`. -/
theorem contMixingTimeFrom_anti (A : WAdj (V := V)) (x : V) {ε δ : ℝ}
    (hεδ : ε ≤ δ)
    (hne : ∃ t : ℝ, 0 ≤ t ∧ ∀ s : ℝ, t ≤ s →
      tvDistance (contWalkDistribution A s x) (stationaryVec A) ≤ ε) :
    contMixingTimeFrom A x δ ≤ contMixingTimeFrom A x ε :=
  csInf_le_csInf (contMixingTimeFrom_bddBelow A x δ) hne
    (fun _ ht => ⟨ht.1, fun s hs => (ht.2 s hs).trans hεδ⟩)

/-!
## The Poisson bridge: continuous↔discrete comparability

`proposals/continuous-time-chi-square-mixing.md`'s named follow-on
(2026-09-01): LPW ch. 20's Poissonization — the continuous-time walk law
is the Poisson mixture of the discrete walk laws — and the TV
comparability it yields. The identity
`ν^cont_t = ∑'_k e^{−t}tᵏ/k! · ν_k` is proved through the exponential
split `−t(I − P) = tP − tI` (`Matrix.exp_add_of_commute`, the scalar
matrix commutes with everything) and the scalar-matrix exponential
`e^{−tI} = e^{−t} • I` (`Heat.matrix_exp_smul_one`). The TV toolkit (the
`Pᵀ` ℓ¹-contraction and discrete TV monotonicity) is field-standard and
new to the shelf; the comparability
`TV_cont(t) ≤ ∑_{k<m} e^{−t}tᵏ/k! + TV_disc(m)` splits the mixture at
any threshold; the transfer corollary is the would-be consumer of the
still-deferred discrete `t_mix` object. All proved, zero axioms.
-/

/-! ## The Poisson weight (destined for `Mixing.lean`) -/

/-- The Poisson weight at time `t`: `e^{−t}·tᵏ/k!` — the probability
that a rate-one Poisson clock rings exactly `k` times by time `t`. The
mixture weights of the Poissonization identity. -/
noncomputable def poissonWeight (t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-t) * t ^ k / (Nat.factorial k : ℝ)

theorem poissonWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ poissonWeight t k := by
  unfold poissonWeight
  positivity

/-- The Poisson weights are a probability sequence:
`∑' poissonWeight t = 1` at every time (negative times included) —
`e^{−t} · e^{t} = 1`. -/
theorem poissonWeight_hasSum_one (t : ℝ) :
    HasSum (poissonWeight t) 1 := by
  have hcore : HasSum (fun k => Real.exp (-t) * t ^ k / (Nat.factorial k : ℝ)) 1 := by
    apply (hasSum_mul_left_iff (Real.exp_ne_zero t)).mp
    simp only [mul_one]
    have hfun : (fun k => Real.exp t * (Real.exp (-t) * t ^ k
          / (Nat.factorial k : ℝ)))
        = fun k => t ^ k / (Nat.factorial k : ℝ) := by
      funext k
      rw [mul_div_assoc, Real.exp_neg, ← mul_assoc, ← div_eq_mul_inv,
        div_self (Real.exp_ne_zero t), one_mul]
    rw [hfun, Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ t
  have heq : poissonWeight t = fun k => Real.exp (-t) * t ^ k
      / (Nat.factorial k : ℝ) := rfl
  rw [heq]
  exact hcore

theorem poissonWeight_summable (t : ℝ) : Summable (poissonWeight t) :=
  (poissonWeight_hasSum_one t).summable

theorem poissonWeight_tsum_eq_one (t : ℝ) :
    ∑' k, poissonWeight t k = 1 :=
  (poissonWeight_hasSum_one t).tsum_eq

/-! ## The Poissonization identity -/

/-- The discrete density at `k` is the `k`-th walk power applied to the
initial density — the uncentered twin of `walkDensity_sub_one`. -/
theorem walkDensity_eq_pow_walkTransitionMatrix_mulVec
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (k : ℕ) (x : V) :
    walkDensity A k x
      = (walkTransitionMatrix A ^ k) *ᵥ walkDensity A 0 x := by
  induction k with
  | zero => simp [walkDensity, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [walkDensity_succ A hA hd k x, ih, pow_succ',
      ← Matrix.mulVec_mulVec]

/-- **The Poissonized density**: the continuous-time walk density is the
Poisson mixture of the discrete densities —
`e^{−tL_walk} *ᵥ h₀ = ∑' k, poissonWeight t k • h_k`. Route: the
exponential split `−t(I − P) = tP − tI` through
`Matrix.exp_add_of_commute` (the scalar matrix `−tI` commutes with
everything), the scalar-matrix exponential `e^{−tI} = e^{−t} • I`, and
the shelf's `expSeries_hasSum_exp` at `tP` mapped through `*ᵥ h₀` with
the power identity `(tP)ᵏ = tᵏ • Pᵏ`. -/
theorem hasSum_poisson_walkDensity (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℝ) (x : V) :
    HasSum (fun k : ℕ => poissonWeight t k • walkDensity A k x)
      (walkHeatKernel A t *ᵥ walkDensity A 0 x) := by
  have hsplit : -(t • walkLaplacian A)
      = (t • walkTransitionMatrix A) + -((t : ℝ) • (1 : Matrix V V ℝ)) := by
    rw [walkLaplacian, smul_sub, neg_sub, sub_eq_add_neg]
  have hcomm : Commute ((t : ℝ) • walkTransitionMatrix A)
      (-((t : ℝ) • (1 : Matrix V V ℝ))) := by
    show (t • walkTransitionMatrix A) * -((t : ℝ) • (1 : Matrix V V ℝ))
      = -((t : ℝ) • (1 : Matrix V V ℝ)) * (t • walkTransitionMatrix A)
    have hn : -((t : ℝ) • (1 : Matrix V V ℝ))
        = (-(t : ℝ)) • (1 : Matrix V V ℝ) := by rw [neg_smul]
    rw [hn, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, smul_smul, one_mul, mul_one]
    congr 1
    ring
  have hadd := Matrix.exp_add_of_commute ℝ ((t : ℝ) • walkTransitionMatrix A)
    (-((t : ℝ) • (1 : Matrix V V ℝ))) hcomm
  have hscalar : NormedSpace.exp ℝ (-((t : ℝ) • (1 : Matrix V V ℝ)))
      = Real.exp (-t) • 1 := by
    rw [← neg_smul, matrix_exp_smul_one]
  have hstep : walkHeatKernel A t *ᵥ walkDensity A 0 x
      = Real.exp (-t)
          • (NormedSpace.exp ℝ ((t : ℝ) • walkTransitionMatrix A)
            *ᵥ walkDensity A 0 x) := by
    rw [walkHeatKernel, hsplit, hadd, hscalar, ← Matrix.mulVec_mulVec,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Matrix.mulVec_smul]
  have h := (expSeries_hasSum_exp ((t : ℝ) • walkTransitionMatrix A)).map
    ({ toFun := fun N => N *ᵥ walkDensity A 0 x
       map_zero' := by simp [Matrix.zero_mulVec]
       map_add' := fun N₁ N₂ => by simp [Matrix.add_mulVec] } :
      Matrix V V ℝ →+ (V → ℝ))
    (by
      refine continuous_pi fun i => ?_
      have hcont : Continuous fun N : Matrix V V ℝ
          => ∑ j, N i j * walkDensity A 0 x j := by
        refine continuous_finset_sum _ fun j _ => ?_
        exact ((continuous_apply j).comp (continuous_apply i)).mul
          continuous_const
      simpa only [Matrix.mulVec, Matrix.dotProduct] using hcont)
  have h' : HasSum (fun k : ℕ =>
        ((Nat.factorial k : ℝ)⁻¹ • ((t : ℝ) • walkTransitionMatrix A) ^ k)
          *ᵥ walkDensity A 0 x)
      (NormedSpace.exp ℝ ((t : ℝ) • walkTransitionMatrix A)
        *ᵥ walkDensity A 0 x) := h
  have hterm : ∀ k : ℕ,
      Real.exp (-t) • (((Nat.factorial k : ℝ)⁻¹
        • ((t : ℝ) • walkTransitionMatrix A) ^ k) *ᵥ walkDensity A 0 x)
      = poissonWeight t k • walkDensity A k x := by
    intro k
    rw [pow_smul_matrix, Matrix.smul_mulVec_assoc, Matrix.smul_mulVec_assoc,
      smul_smul, smul_smul,
      walkDensity_eq_pow_walkTransitionMatrix_mulVec A hA hd k x]
    unfold poissonWeight
    rw [div_eq_inv_mul]
    congr 1
    ring
  have hsm := h'.const_smul (Real.exp (-t))
  simp only [hterm] at hsm
  rw [hstep]
  exact hsm

/-- **The Poissonization identity** at the density level. -/
theorem contWalkDensity_eq_tsum (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℝ) (x : V) :
    contWalkDensity A t x
      = fun i => ∑' k : ℕ, poissonWeight t k * walkDensity A k x i := by
  funext i
  have h := ((Pi.hasSum.mp (hasSum_poisson_walkDensity A hA hd t x)) i)
  calc contWalkDensity A t x i
      = (walkHeatKernel A t *ᵥ walkDensity A 0 x) i := rfl
    _ = ∑' k : ℕ, poissonWeight t k * walkDensity A k x i := by
        rw [← h.tsum_eq]
        exact tsum_congr fun k => by rw [Pi.smul_apply, smul_eq_mul]

/-- **The Poissonization identity** at the law level: the continuous-time
walk law is the Poisson mixture of the discrete walk laws —
`ν^cont_t = ∑'_k e^{−t}tᵏ/k! · ν_k`. LPW ch. 20's `H_t = e^{−t}∑ tᵏ/k! Pᵏ`
read at the law level. -/
theorem contWalkDistribution_eq_tsum (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℝ) (x : V) :
    contWalkDistribution A t x
      = fun i => ∑' k : ℕ, poissonWeight t k * walkDistribution A k x i := by
  funext i
  have hpos : stationaryVec A i ≠ 0 := ne_of_gt (stationaryVec_pos A hd i)
  show stationaryVec A i * contWalkDensity A t x i
      = ∑' k : ℕ, poissonWeight t k * walkDistribution A k x i
  rw [contWalkDensity_eq_tsum A hA hd t x]
  show stationaryVec A i * ∑' k : ℕ, poissonWeight t k * walkDensity A k x i = _
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by
    rw [walkDensity]
    field_simp

/-! ## The TV contraction toolkit -/

omit [DecidableEq V] in
/-- The total-variation distance between two probability vectors is at
most one — the diameter of the probability simplex in this metric. -/
theorem tvDistance_le_one_of_nonneg_of_sum_eq_one {μ ν : V → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1)
    (hν : ∀ i, 0 ≤ ν i) (hν1 : ∑ i, ν i = 1) :
    tvDistance μ ν ≤ 1 := by
  have hpt : ∀ i : V, |μ i - ν i| ≤ μ i + ν i := by
    intro i
    exact abs_le.2 ⟨by linarith [hμ i, hν i], by linarith [hμ i, hν i]⟩
  have hsum : ∑ i, |μ i - ν i| ≤ ∑ i, (μ i + ν i) :=
    Finset.sum_le_sum fun i _ => hpt i
  rw [Finset.sum_add_distrib, hμ1, hν1] at hsum
  rw [tvDistance]
  linarith

/-- The walk law's TV distance to stationarity is at most one at every
time (both are probability vectors under the standing hypotheses). -/
theorem walkDistribution_tvDistance_le_one (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ)
    (x : V) :
    tvDistance (walkDistribution A t x) (stationaryVec A) ≤ 1 :=
  tvDistance_le_one_of_nonneg_of_sum_eq_one
    (walkDistribution_nonneg A hnn hd t x)
    (sum_walkDistribution A hd t x)
    (fun i => le_of_lt (stationaryVec_pos A hd i))
    (sum_stationaryVec A hd)

/-- **The adjoint walk is an ℓ¹-contraction**: applying `(Pᵀ)` to both
arguments never increases the TV distance — the distributional action of
one walk step is a contraction, since every row of `P` is a probability
vector and the triangle inequality averages against them. The engine of
discrete TV monotonicity. -/
theorem tvDistance_walkTransitionMatrixTranspose_mulVec_le
    (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (μ ν : V → ℝ) :
    tvDistance ((walkTransitionMatrix A)ᵀ *ᵥ μ)
        ((walkTransitionMatrix A)ᵀ *ᵥ ν)
      ≤ tvDistance μ ν := by
  have htri : ∀ i : V,
      |((walkTransitionMatrix A)ᵀ *ᵥ (μ - ν)) i|
      ≤ ∑ j, walkTransitionMatrix A j i * |(μ - ν) j| := by
    intro i
    have h0 := Finset.abs_sum_le_sum_abs
      (fun j => (walkTransitionMatrix A)ᵀ i j * (μ - ν) j) Finset.univ
    have hrw : ∀ j : V,
        |(walkTransitionMatrix A)ᵀ i j * (μ - ν) j|
        = walkTransitionMatrix A j i * |(μ - ν) j| := by
      intro j
      rw [Matrix.transpose_apply, abs_mul,
        abs_of_nonneg (walkTransitionMatrix_nonneg A hnn hd j i)]
    simp only [Matrix.mulVec, Matrix.dotProduct] at h0
    rw [Finset.sum_congr rfl fun j _ => hrw j] at h0
    exact h0
  have hflip : ∑ i, ∑ j, walkTransitionMatrix A j i * |(μ - ν) j|
      = ∑ i, |(μ - ν) i| := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by
      rw [← Finset.sum_mul, walkTransitionMatrix_row_sum A hd j, one_mul]
  have hkey : ∑ i, |((walkTransitionMatrix A)ᵀ *ᵥ (μ - ν)) i|
      ≤ ∑ i, |(μ - ν) i| := by
    calc ∑ i, |((walkTransitionMatrix A)ᵀ *ᵥ (μ - ν)) i|
        ≤ ∑ i, ∑ j, walkTransitionMatrix A j i * |(μ - ν) j| :=
          Finset.sum_le_sum fun i _ => htri i
      _ = ∑ i, |(μ - ν) i| := hflip
  have hsplit : ((walkTransitionMatrix A)ᵀ *ᵥ μ)
      - ((walkTransitionMatrix A)ᵀ *ᵥ ν)
      = (walkTransitionMatrix A)ᵀ *ᵥ (μ - ν) := (Matrix.mulVec_sub _ _ _).symm
  have hL : tvDistance ((walkTransitionMatrix A)ᵀ *ᵥ μ)
        ((walkTransitionMatrix A)ᵀ *ᵥ ν)
      = (1/2) * ∑ i, |((walkTransitionMatrix A)ᵀ *ᵥ (μ - ν)) i| := by
    rw [tvDistance]
    exact congrArg (fun s => (1/2) * s)
      (Finset.sum_congr rfl fun i _ => congrArg abs (congrFun hsplit i))
  rw [hL, tvDistance]
  exact mul_le_mul_of_nonneg_left hkey (by norm_num)

/-- The iterated contraction: the `k`-th adjoint-walk power is a TV
contraction — the one-step lemma composed along the power. -/
theorem tvDistance_walkTransitionMatrixTranspose_pow_mulVec_le
    (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (k : ℕ) (μ ν : V → ℝ) :
    tvDistance ((walkTransitionMatrix A)ᵀ ^ k *ᵥ μ)
        ((walkTransitionMatrix A)ᵀ ^ k *ᵥ ν)
      ≤ tvDistance μ ν := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : ∀ w : V → ℝ,
        (walkTransitionMatrix A)ᵀ ^ (k + 1) *ᵥ w
          = (walkTransitionMatrix A)ᵀ *ᵥ ((walkTransitionMatrix A)ᵀ ^ k *ᵥ w) := by
      intro w
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hstep μ, hstep ν]
    exact le_trans
      (tvDistance_walkTransitionMatrixTranspose_mulVec_le A hnn hd _ _) ih

/-- Stationarity iterated: the `k`-th adjoint-walk power fixes the
stationary vector. -/
theorem walkTransitionMatrixTranspose_pow_mulVec_stationaryVec
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (k : ℕ) :
    (walkTransitionMatrix A)ᵀ ^ k *ᵥ stationaryVec A = stationaryVec A := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, walk_isStationary A hA hd, ih]

/-- The law's power evolution: `ν_{t+s} = (Pᵀ)ˢ *ᵥ ν_t`. -/
theorem walkDistribution_add (A : WAdj (V := V)) (t s : ℕ) (x : V) :
    walkDistribution A (t + s) x
      = (walkTransitionMatrix A)ᵀ ^ s *ᵥ walkDistribution A t x := by
  induction s with
  | zero => simp
  | succ s ih =>
    calc walkDistribution A (t + (s + 1)) x
        = (walkTransitionMatrix A)ᵀ *ᵥ walkDistribution A (t + s) x := by
          rw [show t + (s + 1) = t + s + 1 from (Nat.add_assoc t s 1).symm,
            walkDistribution_succ]
      _ = (walkTransitionMatrix A)ᵀ *ᵥ ((walkTransitionMatrix A)ᵀ ^ s
            *ᵥ walkDistribution A t x) := by rw [ih]
      _ = (walkTransitionMatrix A)ᵀ ^ (s + 1)
            *ᵥ walkDistribution A t x := by
          rw [pow_succ', ← Matrix.mulVec_mulVec]

/-- **Discrete TV monotonicity in time**: waiting longer never increases
the walk law's TV distance to stationarity — the contraction composed
with iterated stationarity. Field-standard (`d(k)` non-increasing), and
the certificate the comparability split consumes. -/
theorem walkDistribution_tvDistance_anti (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (t s : ℕ) (x : V) :
    tvDistance (walkDistribution A (t + s) x) (stationaryVec A)
      ≤ tvDistance (walkDistribution A t x) (stationaryVec A) := by
  have key := tvDistance_walkTransitionMatrixTranspose_pow_mulVec_le A hnn hd s
    (walkDistribution A t x) (stationaryVec A)
  rwa [walkTransitionMatrixTranspose_pow_mulVec_stationaryVec A hA hd s,
    ← walkDistribution_add A t s x] at key

/-! ## TV convexity in mixtures, and the comparability -/

/-- **Splitting a summable series at a threshold**: the head–tail
decomposition at `m`, by iterated `tsum_eq_zero_add` (the pinned
Mathlib has no direct `Finset.range` split at this generality). -/
theorem tsum_eq_range_add (f : ℕ → ℝ) (hsm : Summable f) (m : ℕ) :
    ∑' k, f k = ∑ k in Finset.range m, f k + ∑' k, f (k + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have htail : Summable fun k => f (k + m) :=
      hsm.comp_injective fun a b hab => by simpa using congrArg (· + m) hab
    have htail2 : ∑' b : ℕ, f (b + 1 + m) = ∑' k : ℕ, f (k + (m + 1)) :=
      tsum_congr fun k => congrArg f (by ring_nf)
    rw [Finset.sum_range_succ, ih, tsum_eq_zero_add htail,
      show Nat.zero + m = m from Nat.zero_add m, htail2]
    ring

omit [DecidableEq V] in
/-- **TV convexity in countable mixtures**: if `c` is a probability
sequence and every `ν k` a probability vector, the TV distance from the
mixture to `π` is at most the `c`-weighted average of the TV distances —
the triangle inequality averaged against the mixture weights. The
Poissonization consumer. -/
theorem tvDistance_tsum_le {c : ℕ → ℝ} {ν : ℕ → V → ℝ} {π : V → ℝ}
    (hc : ∀ k, 0 ≤ c k) (hc1 : HasSum c 1)
    (hπ : ∀ i, 0 ≤ π i) (hπ1 : ∑ i, π i = 1)
    (hν : ∀ k i, 0 ≤ ν k i) (hν1 : ∀ k, ∑ i, ν k i = 1) :
    tvDistance (fun i => ∑' k, c k * ν k i) π
      ≤ ∑' k, c k * tvDistance (ν k) π := by
  have hνle : ∀ k i, ν k i ≤ 1 := fun k i =>
    le_trans (Finset.single_le_sum (fun j _ => hν k j) (Finset.mem_univ i))
      (hν1 k).le
  have hπle : ∀ i, π i ≤ 1 := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => hπ j) (Finset.mem_univ i))
      hπ1.le
  have habs : ∀ k i, |ν k i - π i| ≤ 1 := by
    intro k i
    exact abs_le.2 ⟨by linarith [hν k i, hπle i],
      by linarith [hνle k i, hπ i]⟩
  have hcsm : Summable c := hc1.summable
  have hsmν : ∀ i, Summable fun k => c k * ν k i := fun i =>
    Summable.of_norm_bounded c hcsm fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc k),
        abs_of_nonneg (hν k i)]
      simpa using mul_le_mul_of_nonneg_left (hνle k i) (hc k)
  have hsmabs : ∀ i, Summable fun k => c k * |ν k i - π i| := fun i =>
    Summable.of_norm_bounded c hcsm fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc k), abs_abs]
      simpa using mul_le_mul_of_nonneg_left (habs k i) (hc k)
  have hcent : ∀ i : V,
      (∑' k, c k * ν k i) - π i = ∑' k, c k * (ν k i - π i) := by
    intro i
    have hA : HasSum (fun k => c k * ν k i) (∑' k, c k * ν k i) :=
      (hsmν i).hasSum
    have hB : HasSum (fun k => c k * π i) (π i) := by
      have h := hc1.mul_right (π i)
      simpa using h
    have hsub : HasSum (fun k => c k * ν k i - c k * π i)
        ((∑' k, c k * ν k i) - π i) := hA.sub hB
    simp only [← mul_sub] at hsub
    exact hsub.tsum_eq.symm
  have htri2 : ∀ i : V,
      |(∑' k, c k * ν k i) - π i| ≤ ∑' k, c k * |ν k i - π i| := by
    intro i
    rw [hcent i]
    have hrew : ∀ k : ℕ,
        ‖c k * (ν k i - π i)‖ = c k * |ν k i - π i| := by
      intro k
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc k)]
    have hsmn : Summable fun k => ‖c k * (ν k i - π i)‖ := by
      have h := hsmabs i
      rwa [show (fun k => c k * |ν k i - π i|)
        = fun k => ‖c k * (ν k i - π i)‖
          from funext fun k => (hrew k).symm] at h
    refine (norm_tsum_le_tsum_norm
      (f := fun k => c k * (ν k i - π i)) hsmn).trans_eq ?_
    exact tsum_congr fun k => hrew k
  have hswap : ∑ i, ∑' k, c k * |ν k i - π i|
      = ∑' k, ∑ i, c k * |ν k i - π i| :=
    (tsum_sum (fun i _ => hsmabs i)).symm
  have hinner : ∀ k : ℕ, ∑ i, c k * |ν k i - π i|
      = c k * (2 * tvDistance (ν k) π) := by
    intro k
    have h2 : 2 * tvDistance (ν k) π = ∑ i, |ν k i - π i| := by
      rw [tvDistance, ← mul_assoc,
        show (2 : ℝ) * (1/2) = 1 from by norm_num, one_mul]
    rw [h2, ← Finset.mul_sum]
  have hsmTV : Summable fun k => c k * tvDistance (ν k) π :=
    Summable.of_norm_bounded c hcsm fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc k),
        abs_of_nonneg (tvDistance_nonneg _ _)]
      calc c k * tvDistance (ν k) π
          ≤ c k * 1 := mul_le_mul_of_nonneg_left
            (tvDistance_le_one_of_nonneg_of_sum_eq_one (hν k) (hν1 k)
              hπ hπ1) (hc k)
        _ = c k := mul_one _
  have hsm2 : Summable fun k => c k * (2 * tvDistance (ν k) π) := by
    simpa only [smul_eq_mul, mul_left_comm] using hsmTV.const_smul (2 : ℝ)
  have hhalf := (hsm2.hasSum).const_smul ((1/2 : ℝ))
  have hcongr : ∀ k : ℕ, (1/2 : ℝ) • (c k * (2 * tvDistance (ν k) π))
      = c k * tvDistance (ν k) π := by
    intro k
    rw [smul_eq_mul]
    ring
  simp only [hcongr] at hhalf
  rw [tvDistance]
  calc (1/2) * ∑ i, |(∑' k, c k * ν k i) - π i|
      ≤ (1/2) * ∑ i, ∑' k, c k * |ν k i - π i| :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => htri2 i) (by norm_num)
    _ = (1/2) * ∑' k, c k * (2 * tvDistance (ν k) π) := by
        rw [hswap]
        exact congrArg (fun s => (1/2) * s) (tsum_congr hinner)
    _ = ∑' k, c k * tvDistance (ν k) π := by
        rw [show ((1/2 : ℝ) * ∑' k, c k * (2 * tvDistance (ν k) π))
            = (1/2 : ℝ) • ∑' k, c k * (2 * tvDistance (ν k) π) from rfl,
          ← hhalf.tsum_eq]

/-- **The Poisson-averaged TV bound**: the continuous walk law's TV
distance to stationarity is at most the Poisson average of the discrete
TV distances. -/
theorem contWalkDistribution_tvDistance_le_tsum (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] {t : ℝ} (ht : 0 ≤ t) (x : V) :
    tvDistance (contWalkDistribution A t x) (stationaryVec A)
      ≤ ∑' k, poissonWeight t k
          * tvDistance (walkDistribution A k x) (stationaryVec A) := by
  rw [contWalkDistribution_eq_tsum A hA hd t x]
  exact tvDistance_tsum_le (poissonWeight_nonneg ht)
    (poissonWeight_hasSum_one t)
    (fun i => le_of_lt (stationaryVec_pos A hd i)) (sum_stationaryVec A hd)
    (fun k i => walkDistribution_nonneg A hnn hd k x i)
    (fun k => sum_walkDistribution A hd k x)

set_option maxHeartbeats 800000 in
/-- **The continuous↔discrete TV comparability**: at every threshold
`m`, the continuous-time TV distance at time `t` is at most the Poisson
lower-tail weight below `m` plus the discrete TV distance at `m` — LPW
ch. 20's Poissonization comparison, with the tail term exact (no
Chernoff rounding). At `m = 0` this is the worst-start bound
`TV_cont(t) ≤ TV(δ_x, π)`; at `t = 0` it degrades to the trivial
`TV ≤ 1 + TV₀`. -/
theorem contWalkDistribution_tvDistance_add_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (x : V) :
    tvDistance (contWalkDistribution A t x) (stationaryVec A)
      ≤ ∑ k in Finset.range m, poissonWeight t k
        + tvDistance (walkDistribution A m x) (stationaryVec A) := by
  have hFsm : Summable fun k => poissonWeight t k
      * tvDistance (walkDistribution A k x) (stationaryVec A) :=
    Summable.of_norm_bounded (poissonWeight t) (poissonWeight_summable t)
      fun k => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (poissonWeight_nonneg ht k),
          abs_of_nonneg (tvDistance_nonneg _ _)]
        simpa using mul_le_mul_of_nonneg_left
          (walkDistribution_tvDistance_le_one A hnn hd k x)
          (poissonWeight_nonneg ht k)
  have hTV := contWalkDistribution_tvDistance_le_tsum A hA hnn hd ht x
  rw [tsum_eq_range_add _ hFsm m] at hTV
  have hone : ∑ k in Finset.range m, poissonWeight t k
      + ∑' k, poissonWeight t (k + m) = 1 := by
    have h := tsum_eq_range_add (poissonWeight t)
      (poissonWeight_summable t) m
    rw [poissonWeight_tsum_eq_one t] at h
    exact h.symm
  have hhead : ∑ k in Finset.range m,
      (poissonWeight t k
        * tvDistance (walkDistribution A k x) (stationaryVec A))
      ≤ ∑ k in Finset.range m, poissonWeight t k := by
    refine Finset.sum_le_sum fun k _ => ?_
    simpa using mul_le_mul_of_nonneg_left
      (walkDistribution_tvDistance_le_one A hnn hd k x)
      (poissonWeight_nonneg ht k)
  have htail : ∑' k,
      (poissonWeight t (k + m)
        * tvDistance (walkDistribution A (k + m) x) (stationaryVec A))
      ≤ tvDistance (walkDistribution A m x) (stationaryVec A) := by
    have hsmw : Summable fun k => poissonWeight t (k + m) :=
      (poissonWeight_summable t).comp_injective
        fun a b hab => by simpa using congrArg (· + m) hab
    have hsmL : Summable fun i => poissonWeight t (i + m)
        * tvDistance (walkDistribution A (i + m) x) (stationaryVec A) :=
      Summable.of_norm_bounded (fun i => poissonWeight t (i + m)) hsmw
        fun i => by
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (poissonWeight_nonneg ht (i + m)),
            abs_of_nonneg (tvDistance_nonneg _ _)]
          simpa using mul_le_mul_of_nonneg_left
            (walkDistribution_tvDistance_le_one A hnn hd (i + m) x)
            (poissonWeight_nonneg ht (i + m))
    have hle : ∀ k : ℕ,
        poissonWeight t (k + m)
          * tvDistance (walkDistribution A (k + m) x) (stationaryVec A)
        ≤ poissonWeight t (k + m)
            * tvDistance (walkDistribution A m x) (stationaryVec A) := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ (poissonWeight_nonneg ht (k + m))
      have hanti := walkDistribution_tvDistance_anti A hA hnn hd m k x
      rw [Nat.add_comm m k] at hanti
      exact hanti
    have hstep : ∑' k,
        (poissonWeight t (k + m)
          * tvDistance (walkDistribution A (k + m) x) (stationaryVec A))
        ≤ ∑' k,
          (poissonWeight t (k + m)
            * tvDistance (walkDistribution A m x) (stationaryVec A)) :=
      tsum_le_tsum hle hsmL
        (hsmw.mul_right (tvDistance (walkDistribution A m x) (stationaryVec A)))
    have htailw : ∑' k, poissonWeight t (k + m) ≤ 1 := by
      have hnn2 : 0 ≤ ∑ k in Finset.range m, poissonWeight t k :=
        Finset.sum_nonneg fun k _ => poissonWeight_nonneg ht k
      linarith
    calc ∑' k, (poissonWeight t (k + m)
          * tvDistance (walkDistribution A (k + m) x)
            (stationaryVec A))
        ≤ ∑' k, (poissonWeight t (k + m)
            * tvDistance (walkDistribution A m x) (stationaryVec A)) :=
          hstep
      _ ≤ tvDistance (walkDistribution A m x) (stationaryVec A) := by
          rw [tsum_mul_right]
          nlinarith [htailw,
            tvDistance_nonneg (walkDistribution A m x) (stationaryVec A)]
  linarith

/-- **The discrete-certificate transfer corollary** — the comparability
in certificate form: if the discrete walk is within `ε₁` of stationarity
from time `m` on, and the Poisson lower-tail weight below `m` at time
`t` is at most `ε₂`, then the continuous walk is within `ε₁ + ε₂` at
time `t`. The would-be consumer of the still-deferred discrete `t_mix`
object: `hmix` is exactly its witness condition. -/
theorem contWalkDistribution_tvDistance_le_of_discreteMixing
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    (x : V) {ε₁ ε₂ : ℝ}
    (hmix : ∀ k : ℕ, m ≤ k →
      tvDistance (walkDistribution A k x) (stationaryVec A) ≤ ε₁)
    (htail : ∑ k in Finset.range m, poissonWeight t k ≤ ε₂) :
    tvDistance (contWalkDistribution A t x) (stationaryVec A)
      ≤ ε₁ + ε₂ := by
  refine (contWalkDistribution_tvDistance_add_le A hA hnn hd ht m x).trans ?_
  have h1 : tvDistance (walkDistribution A m x) (stationaryVec A) ≤ ε₁ :=
    hmix m (Nat.le_refl m)
  linarith

end SpectralGraphTheory
