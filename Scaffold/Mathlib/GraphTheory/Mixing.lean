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
import Scaffold.Mathlib.InformationTheory.Entropy
import Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence

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
- `tvDistance_le_sqrt_half_klDiv`, `klDiv_walkDistribution_le`,
  `klDiv_contWalkDistribution_le` (2026-09-01,
  `proposals/entropy-mixing-pinsker.md`): **Pinsker's inequality** in
  the shelf's vector TV form and the **entropy-decay** family — the
  entropy leg of the mixing program, the third classical distance
  (beside TV and χ²) with a decay bound and a floor
  (`Oversmoothing.lean`'s `klDiv_walkDistribution_ge_of_eigenpair`).
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

The lazy-walk section (2026-09-01,
`proposals/lazy-walk-mixing.md`) adds the lazy operator
`lazyWalkTransitionMatrix = (P + 1)/2` with its law/density/χ² objects
and the intrinsic-rate mixing family
`lazyChiSquareDistance_le_of_connected` (plus TV and entropy
corollaries) — the discrete program's periodicity fix, with the
signless-Laplacian SOS engine `eigvalOf_normalizedLaplacian_le_two`
(`μ ≤ 2`) as its new inner layer.
-/

namespace SpectralGraphTheory

open Matrix Scaffold.LinearAlgebra

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

/-- **A single coordinate's deviation is at most the TV distance** (at
equal masses): the zero-mass triangle route — the deviation mass on the
complement of `i` sums to exactly `−d i`, so `2|d i| = |d i| +
|∑_{j≠i} d j| ≤ ∑_j |d j| = 2·TV`. The constant is sharp (equality
whenever the deviation mass is single-signed, e.g. at a Dirac-vs-uniform
pair); this is the entrywise extraction through a *TV-level* rate — the
directed mixing bias term's engine (`EmpiricalStationary.lean`'s
PageRank capstone), since the directed program bounds TV, not χ². QA:
`Scaffold.QA.SpectralGraph.PR_entrywise_both_QA` (both sides pinned
`1/4`, equality attained at `t = 1` on the Google 2-cycle fixture). -/
theorem abs_sub_le_tvDistance {μ ν : V → ℝ}
    (hmass : ∑ i, μ i = ∑ i, ν i) (i : V) :
    |μ i - ν i| ≤ tvDistance μ ν := by
  have hzero : ∑ j, (μ - ν) j = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hmass, sub_self]
  have hpart : ∑ j, (μ - ν) j
      = (μ - ν) i + ∑ j in Finset.univ.erase i, (μ - ν) j := by
    conv_lhs => rw [show (Finset.univ : Finset V)
        = insert i (Finset.univ.erase i) from
        (Finset.insert_erase (Finset.mem_univ i)).symm]
    rw [Finset.sum_insert (by simp : i ∉ Finset.univ.erase i)]
  have herase : ∑ j in Finset.univ.erase i, (μ - ν) j = -((μ - ν) i) := by
    have hsum' := hpart
    rw [hzero] at hsum'
    linarith
  have htri := Finset.abs_sum_le_sum_abs (fun j => (μ - ν) j)
    (Finset.univ.erase i)
  have hj : ∑ j, |μ j - ν j|
      = |μ i - ν i| + ∑ j in Finset.univ.erase i, |μ j - ν j| := by
    conv_lhs => rw [show (Finset.univ : Finset V)
        = insert i (Finset.univ.erase i) from
        (Finset.insert_erase (Finset.mem_univ i)).symm]
    rw [Finset.sum_insert (by simp : i ∉ Finset.univ.erase i)]
  have hkey : |μ i - ν i| + |μ i - ν i| ≤ ∑ j, |μ j - ν j| := by
    calc |μ i - ν i| + |μ i - ν i|
        = |μ i - ν i| + |∑ j in Finset.univ.erase i, (μ - ν) j| := by
          rw [herase, abs_neg]
          rfl
      _ ≤ |μ i - ν i| + ∑ j in Finset.univ.erase i, |(μ - ν) j| :=
          add_le_add_left htri _
      _ = ∑ j, |μ j - ν j| := by
          rw [hj]
          simp only [Pi.sub_apply]
  unfold tvDistance
  linarith

omit [DecidableEq V] in
/-- **The distinguishing-function bound** — the classical lower-bound
companion of the triangle inequality: a statistic bounded by `1`
distinguishes two vectors by at most twice their total-variation
distance, `|(μ − ν)(f)| ≤ 2 · TV(μ, ν)`. Hypothesis-minimal — no sign
or mass assumptions on `μ`, `ν` (the proof is
`|∑ (μ−ν)·f| ≤ ∑ |μ−ν|·|f| ≤ ∑ |μ−ν|`). This is the engine of every
total-variation *floor*: the upper bound's Cauchy–Schwarz conversion
`tvDistance_le_half_sqrt` has no reverse, and this lemma is the
standard way around that. -/
theorem tvDistance_ge_half_abs_sum {μ ν : V → ℝ} (f : V → ℝ)
    (hc : ∀ i, |f i| ≤ 1) :
    (1/2) * |∑ i, (μ i - ν i) * f i| ≤ tvDistance μ ν := by
  have h1 : |∑ i, (μ i - ν i) * f i| ≤ ∑ i, |(μ i - ν i) * f i| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ i, |(μ i - ν i) * f i| ≤ ∑ i, |μ i - ν i| := by
    refine Finset.sum_le_sum fun i _ => ?_
    calc |(μ i - ν i) * f i| = |μ i - ν i| * |f i| := (abs_mul _ _)
      _ ≤ |μ i - ν i| * 1 :=
          mul_le_mul_of_nonneg_left (hc i) (abs_nonneg _)
      _ = |μ i - ν i| := mul_one _
  rw [tvDistance]
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
## The Doeblin TV contraction (directed, matrix level)

`proposals/doeblin-tv-contraction-pagerank-rate.md` (2026-09-02): the
mixing program's TV toolkit's first *directed-axis* member — and the
now-public Doeblin range engine's second consumer, on a different
mathematical surface (TV between laws, not coordinate convergence to
a limit). A row-stochastic `Q` with every entry `≥ δ` contracts the
total-variation distance between any two equal-mass vectors by
`1 - |V|·δ` (`tvDistance_vecMul_le_of_pos_entries`): the dual/
test-function pairing `z ⬝ᵥ s = w ⬝ᵥ (Q *ᵥ s)` at the sign statistic
`s` routes the evolved difference through the engine's entrywise-range
contraction, with the zero-mass interval pinning
(`abs_dotProduct_le_half_entryRange_mul_sum_abs`) closing the
constant. Hypothesis-minimal: no sign hypothesis on either vector.
The block-iterated form and the positive-power assembly
`tvDistance_vecMul_pow_le_of_pos_power` (any mass-one start against
any mass-one stationary vector — sign-free on both) give the rate
clause the retired `primitive_power_tendsto` deliberately did not
carry, at its proof's own byproduct rate. All proved, zero axioms.
-/

omit [DecidableEq V] in
/-- Mass preservation under a row-stochastic row action: the mass of
`μ ᵥ* M` is the mass of `μ`. -/
theorem sum_vecMul_eq_of_row_sum {M : Matrix V V ℝ}
    (hrow : ∀ i, ∑ j, M i j = 1) (μ : V → ℝ) :
    ∑ j, (μ ᵥ* M) j = ∑ i, μ i := by
  have hflip : ∑ j, (μ ᵥ* M) j = ∑ j, ∑ i, μ i * M i j := rfl
  rw [hflip, Finset.sum_comm]
  exact (Finset.sum_congr rfl fun i _ => by
    rw [← Finset.mul_sum, hrow i, mul_one]).symm

omit [DecidableEq V] in
/-- **Zero-sum interval pinning**: a zero-mass functional `w` pairs with
any function to at most half the function's entrywise range times the
`ℓ¹` mass of `w` — the constant shift dies against zero mass, and what
remains is bounded by the range's half-width. The dual step behind the
Doeblin TV contraction. -/
theorem abs_dotProduct_le_half_entryRange_mul_sum_abs [Nonempty V]
    {w h : V → ℝ} (hwsum : ∑ i, w i = 0) :
    |w ⬝ᵥ h| ≤ (1/2) * entryRange h * ∑ i, |w i| := by
  have hmid : ∀ i : V,
      |h i - (entrySup h + entryInf h) / 2| ≤ entryRange h / 2 := by
    intro i
    have h1 := entryInf_le h i
    have h2 := le_entrySup h i
    unfold entryRange
    rw [abs_le]
    constructor <;> linarith
  have hzero : ∑ i, w i * ((entrySup h + entryInf h) / 2) = 0 := by
    rw [← Finset.sum_mul, hwsum, zero_mul]
  have hsplit : w ⬝ᵥ h
      = ∑ i, w i * (h i - (entrySup h + entryInf h) / 2) := by
    have heq : ∀ i : V, w i * h i
        = w i * (h i - (entrySup h + entryInf h) / 2)
          + w i * ((entrySup h + entryInf h) / 2) := fun _ => by ring
    calc w ⬝ᵥ h = ∑ i, w i * h i := rfl
      _ = ∑ i, (w i * (h i - (entrySup h + entryInf h) / 2)
          + w i * ((entrySup h + entryInf h) / 2)) :=
          Finset.sum_congr rfl fun i _ => heq i
      _ = ∑ i, w i * (h i - (entrySup h + entryInf h) / 2)
          + ∑ i, w i * ((entrySup h + entryInf h) / 2) := Finset.sum_add_distrib
      _ = ∑ i, w i * (h i - (entrySup h + entryInf h) / 2) := by
          rw [hzero, add_zero]
  calc |w ⬝ᵥ h| = |∑ i, w i * (h i - (entrySup h + entryInf h) / 2)| := by
        rw [hsplit]
    _ ≤ ∑ i, |w i * (h i - (entrySup h + entryInf h) / 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * (entryRange h / 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc |w i * (h i - (entrySup h + entryInf h) / 2)|
            = |w i| * |h i - (entrySup h + entryInf h) / 2| := abs_mul _ _
          _ ≤ |w i| * (entryRange h / 2) :=
              mul_le_mul_of_nonneg_left (hmid i) (abs_nonneg _)
    _ = (1/2) * entryRange h * ∑ i, |w i| := by rw [← Finset.sum_mul]; ring

omit [DecidableEq V] in
/-- **Stochastic non-expansiveness of TV under the row action**: a
nonnegative row-stochastic matrix never increases the total-variation
distance between two vectors — the row-action twin of the delivered
adjoint-walk `mulVec` contraction below, at the generic-matrix level
(the engine `entryRange_mulVec_le`'s companion, in TV). -/
theorem tvDistance_vecMul_le {M : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j, M i j = 1) (μ ν : V → ℝ) :
    tvDistance (μ ᵥ* M) (ν ᵥ* M) ≤ tvDistance μ ν := by
  have htri : ∀ j : V,
      |((μ - ν) ᵥ* M) j| ≤ ∑ i, |(μ - ν) i| * M i j := by
    intro j
    have h0 := Finset.abs_sum_le_sum_abs
      (fun i => (μ - ν) i * M i j) Finset.univ
    simp only [Matrix.vecMul, Matrix.dotProduct, Matrix.transpose_apply,
      Pi.sub_apply] at h0 ⊢
    calc |∑ i, (μ - ν) i * M i j| ≤ ∑ i, |(μ - ν) i * M i j| := h0
      _ = ∑ i, |(μ - ν) i| * M i j := Finset.sum_congr rfl fun i _ => by
          rw [abs_mul, abs_of_nonneg (hnn i j)]
  have hflip : ∑ j, ∑ i, |(μ - ν) i| * M i j = ∑ i, |(μ - ν) i| := by
    rw [Finset.sum_comm]
    exact (Finset.sum_congr rfl fun i _ => by
      rw [← Finset.mul_sum, hrow i, mul_one]).symm
  have hsplit : (μ ᵥ* M) - (ν ᵥ* M) = (μ - ν) ᵥ* M :=
    (Matrix.sub_vecMul _ _ _).symm
  have hL : tvDistance (μ ᵥ* M) (ν ᵥ* M)
      = (1/2) * ∑ j, |((μ - ν) ᵥ* M) j| := by
    rw [tvDistance]
    exact congrArg (fun s => (1/2) * s)
      (Finset.sum_congr rfl fun j _ => congrArg abs (congrFun hsplit j))
  have hkey : ∑ j, |((μ - ν) ᵥ* M) j| ≤ ∑ i, |(μ - ν) i| :=
    le_trans (Finset.sum_le_sum fun j _ => htri j) hflip.le
  rw [hL, tvDistance]
  exact mul_le_mul_of_nonneg_left hkey (by norm_num)

omit [DecidableEq V] in
/-- **The Doeblin TV contraction.** A row-stochastic matrix whose
entries are all at least `δ` contracts the total-variation distance
between any two *equal-mass* vectors by the coefficient
`1 - |V|·δ` — the classical Doeblin/Dobrushin bound at the law level
(the same mechanism as the undirected uniform-`t_mix`
submultiplicativity family, now at the entrywise floor). Hypothesis-
minimal: no sign hypothesis on either vector (only the equal-mass
pinning, which the proof makes zero-mass). The route is the dual/
test-function pairing: `TV = (1/2)·(z ⬝ᵥ s)` at the sign statistic
`s`, `z ⬝ᵥ s = w ⬝ᵥ (Q *ᵥ s)` by `Matrix.dotProduct_mulVec`, and the
`Q *ᵥ s` entrywise range contracts by the engine
`entryRange_mulVec_le_of_pos_entries` — the engine's second consumer,
on a different mathematical surface (TV between laws, not coordinate
convergence to a limit).

QA: `DirectedMixing_QA`'s mechanism section pins this attained
exactly on the strictly positive `2×2` fixture and refutes the
floor-free form on the permutation fixture. -/
theorem tvDistance_vecMul_le_of_pos_entries [Nonempty V]
    {Q : Matrix V V ℝ} (hrow : ∀ i, ∑ j, Q i j = 1) {δ : ℝ}
    (hle : ∀ i j, δ ≤ Q i j) (μ ν : V → ℝ)
    (hsum : ∑ i, μ i = ∑ i, ν i) :
    tvDistance (μ ᵥ* Q) (ν ᵥ* Q)
      ≤ (1 - (Fintype.card V : ℝ) * δ) * tvDistance μ ν := by
  have hρnn : 0 ≤ 1 - (Fintype.card V : ℝ) * δ := by
    obtain ⟨i₀⟩ := ‹Nonempty V›
    have h2 : (Fintype.card V : ℝ) * δ ≤ 1 :=
      calc (Fintype.card V : ℝ) * δ = ∑ j : V, δ := by simp
        _ ≤ ∑ j, Q i₀ j := Finset.sum_le_sum fun j _ => hle i₀ j
        _ = 1 := hrow i₀
    linarith
  -- the sign statistic of the evolved difference
  have hsign : ∀ j : V,
      ((μ - ν) ᵥ* Q) j * (if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1)
        = |((μ - ν) ᵥ* Q) j| := by
    intro j
    by_cases h : ((μ - ν) ᵥ* Q) j < 0
    · rw [if_pos h, abs_of_neg h]; ring
    · rw [if_neg h, abs_of_nonneg (by linarith)]; ring
  have hz : ∑ j, |((μ - ν) ᵥ* Q) j| = (μ - ν) ᵥ* Q ⬝ᵥ
      (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1) := by
    simp only [Matrix.dotProduct]
    exact Finset.sum_congr rfl fun j _ => (hsign j).symm
  have hdual : (μ - ν) ᵥ* Q ⬝ᵥ
      (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1)
      = (μ - ν) ⬝ᵥ (Q *ᵥ (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1)) :=
    (Matrix.dotProduct_mulVec _ _ _).symm
  have hR : entryRange (Q *ᵥ
      (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1))
      ≤ (1 - (Fintype.card V : ℝ) * δ) * entryRange
      (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1) :=
    entryRange_mulVec_le_of_pos_entries hrow hle _
  have hsrange : entryRange
      (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1) ≤ 2 := by
    have h1 : entrySup (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1)
        ≤ 1 := (Finset.sup'_le_iff Finset.univ_nonempty _).mpr
      fun j _ => by by_cases h : ((μ - ν) ᵥ* Q) j < 0 <;> simp [h]
    have h2 : -1 ≤ entryInf (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1) :=
      Finset.le_inf' Finset.univ_nonempty _ fun j _ => by
        by_cases h : ((μ - ν) ᵥ* Q) j < 0 <;> simp [h]
    unfold entryRange
    linarith
  have hw0 : ∑ i, (μ - ν) i = 0 := by
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hpin := abs_dotProduct_le_half_entryRange_mul_sum_abs
    (h := Q *ᵥ (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1)) hw0
  have hLnn : 0 ≤ ∑ i, |(μ - ν) i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hR2 : entryRange (Q *ᵥ
      (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1))
      ≤ 2 * (1 - (Fintype.card V : ℝ) * δ) := by
    calc entryRange (Q *ᵥ
        (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1))
        ≤ (1 - (Fintype.card V : ℝ) * δ) * entryRange
          (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1) := hR
      _ ≤ (1 - (Fintype.card V : ℝ) * δ) * 2 :=
          mul_le_mul_of_nonneg_left hsrange hρnn
      _ = 2 * (1 - (Fintype.card V : ℝ) * δ) := by ring
  have hsumz : ∑ j, |((μ - ν) ᵥ* Q) j|
      ≤ (1 - (Fintype.card V : ℝ) * δ) * ∑ i, |(μ - ν) i| := by
    calc ∑ j, |((μ - ν) ᵥ* Q) j| = (μ - ν) ᵥ* Q ⬝ᵥ
        (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1) := hz
      _ = (μ - ν) ⬝ᵥ (Q *ᵥ
          (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1)) := hdual
      _ ≤ |(μ - ν) ⬝ᵥ (Q *ᵥ
          (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1))| :=
          le_abs_self _
      _ ≤ (1/2) * entryRange (Q *ᵥ
          (fun j => if ((μ - ν) ᵥ* Q) j < 0 then (-1 : ℝ) else 1))
          * ∑ i, |(μ - ν) i| := hpin
      _ ≤ (1/2) * (2 * (1 - (Fintype.card V : ℝ) * δ)) * ∑ i, |(μ - ν) i| := by
          refine mul_le_mul_of_nonneg_right ?_ hLnn
          exact mul_le_mul_of_nonneg_left hR2 (by norm_num)
      _ = (1 - (Fintype.card V : ℝ) * δ) * ∑ i, |(μ - ν) i| := by ring
  have hsplit : (μ ᵥ* Q) - (ν ᵥ* Q) = (μ - ν) ᵥ* Q :=
    (Matrix.sub_vecMul _ _ _).symm
  have hL : tvDistance (μ ᵥ* Q) (ν ᵥ* Q)
      = (1/2) * ∑ j, |((μ - ν) ᵥ* Q) j| := by
    rw [tvDistance]
    exact congrArg (fun s => (1/2) * s)
      (Finset.sum_congr rfl fun j _ => congrArg abs (congrFun hsplit j))
  rw [hL, tvDistance]
  simp only [Pi.sub_apply] at hsumz ⊢
  linarith

/-- **The iterated Doeblin TV contraction**: `q` steps of the strictly
positive `Q` contract TV by `(1 - |V|δ)^q` at equal masses. -/
theorem tvDistance_vecMul_pow_le_of_pos_entries [Nonempty V]
    {Q : Matrix V V ℝ} (hrow : ∀ i, ∑ j, Q i j = 1) {δ : ℝ}
    (hle : ∀ i j, δ ≤ Q i j) (μ ν : V → ℝ)
    (hsum : ∑ i, μ i = ∑ i, ν i) (q : ℕ) :
    tvDistance (μ ᵥ* Q ^ q) (ν ᵥ* Q ^ q)
      ≤ (1 - (Fintype.card V : ℝ) * δ) ^ q * tvDistance μ ν := by
  have hρnn : 0 ≤ 1 - (Fintype.card V : ℝ) * δ := by
    obtain ⟨i₀⟩ := ‹Nonempty V›
    have h2 : (Fintype.card V : ℝ) * δ ≤ 1 :=
      calc (Fintype.card V : ℝ) * δ = ∑ j : V, δ := by simp
        _ ≤ ∑ j, Q i₀ j := Finset.sum_le_sum fun j _ => hle i₀ j
        _ = 1 := hrow i₀
    linarith
  induction q with
  | zero => simp [tvDistance, pow_zero, Matrix.vecMul_one, mul_one]
  | succ q ih =>
    have hstep : ∀ x : V → ℝ, x ᵥ* Q ^ (q + 1) = (x ᵥ* Q ^ q) ᵥ* Q := by
      intro x
      rw [pow_succ, Matrix.vecMul_vecMul]
    have hm : ∑ i, (μ ᵥ* Q ^ q) i = ∑ i, (ν ᵥ* Q ^ q) i := by
      rw [sum_vecMul_eq_of_row_sum (pow_row_sum hrow q),
        sum_vecMul_eq_of_row_sum (pow_row_sum hrow q), hsum]
    rw [hstep μ, hstep ν]
    have hone := tvDistance_vecMul_le_of_pos_entries hrow hle _ _ hm
    calc tvDistance ((μ ᵥ* Q ^ q) ᵥ* Q) ((ν ᵥ* Q ^ q) ᵥ* Q)
        ≤ (1 - (Fintype.card V : ℝ) * δ)
          * tvDistance (μ ᵥ* Q ^ q) (ν ᵥ* Q ^ q) := hone
      _ ≤ (1 - (Fintype.card V : ℝ) * δ)
          * ((1 - (Fintype.card V : ℝ) * δ) ^ q * tvDistance μ ν) :=
          mul_le_mul_of_nonneg_left ih hρnn
      _ = (1 - (Fintype.card V : ℝ) * δ) ^ (q + 1) * tvDistance μ ν := by
          rw [pow_succ]; ring

/-- **The Doeblin mixing bound for a positive power.** If the `m`-th
power of the row-stochastic nonnegative `P` is entrywise `≥ δ`, then
after `t` steps any mass-one start is within
`(1 - |V|δ)^(t/m) · TV(ν, π)` of any mass-one stationary `π` — the
rate clause the retired `primitive_power_tendsto` deliberately did not
carry, at its proof's own byproduct rate (explicit, typically loose).
Sign-free on `ν`; `π` enters only through stationarity and mass (no
nonnegativity needed — uniqueness of the stationary vector is a
separate, PF-conditional question this bound does not touch).

QA: `DirectedMixing_QA`'s Google section pins this attained exactly at
every time on the 2-cycle fixture where the plain walk provably never
mixes. -/
theorem tvDistance_vecMul_pow_le_of_pos_power [Nonempty V]
    {P : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) {m : ℕ} {δ : ℝ}
    (hle : ∀ i j, δ ≤ (P ^ m) i j)
    {π : V → ℝ} (hπsum : ∑ i, π i = 1) (hπstat : π ᵥ* P = π)
    {ν : V → ℝ} (hνsum : ∑ i, ν i = 1) (t : ℕ) :
    tvDistance (ν ᵥ* P ^ t) π
      ≤ (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) * tvDistance ν π := by
  have hQrow : ∀ i, ∑ j, (P ^ m) i j = 1 := pow_row_sum hrow m
  have hρnn : 0 ≤ 1 - (Fintype.card V : ℝ) * δ := by
    obtain ⟨i₀⟩ := ‹Nonempty V›
    have h2 : (Fintype.card V : ℝ) * δ ≤ 1 :=
      calc (Fintype.card V : ℝ) * δ = ∑ j : V, δ := by simp
        _ ≤ ∑ j, (P ^ m) i₀ j := Finset.sum_le_sum fun j _ => hle i₀ j
        _ = 1 := hQrow i₀
    linarith
  have hteq : t = t % m + m * (t / m) := (Nat.mod_add_div t m).symm
  have hpow : P ^ t = P ^ (t % m) * P ^ (m * (t / m)) := by
    conv_lhs => rw [hteq]
    rw [pow_add]
  have hsplit : ν ᵥ* P ^ t = (ν ᵥ* P ^ (t % m)) ᵥ* (P ^ m) ^ (t / m) := by
    rw [hpow, ← pow_mul, Matrix.vecMul_vecMul]
  have hmass : ∑ i, (ν ᵥ* P ^ (t % m)) i = ∑ i, π i := by
    rw [sum_vecMul_eq_of_row_sum (pow_row_sum hrow (t % m)), hνsum, hπsum]
  have hπfix : π ᵥ* (P ^ m) ^ (t / m) = π := by
    rw [← pow_mul, vecMul_pow_eq_of_vecMul_eq hπstat]
  have hpair := tvDistance_vecMul_pow_le_of_pos_entries hQrow hle
    (ν ᵥ* P ^ (t % m)) π hmass (t / m)
  have hrem : tvDistance (ν ᵥ* P ^ (t % m)) π ≤ tvDistance ν π := by
    have hstep := tvDistance_vecMul_le (pow_nonneg_entries hnn (t % m))
      (pow_row_sum hrow (t % m)) ν π
    rwa [vecMul_pow_eq_of_vecMul_eq hπstat] at hstep
  calc tvDistance (ν ᵥ* P ^ t) π
      = tvDistance ((ν ᵥ* P ^ (t % m)) ᵥ* (P ^ m) ^ (t / m)) π := by rw [hsplit]
    _ = tvDistance ((ν ᵥ* P ^ (t % m)) ᵥ* (P ^ m) ^ (t / m))
        (π ᵥ* (P ^ m) ^ (t / m)) := by rw [hπfix]
    _ ≤ (1 - (Fintype.card V : ℝ) * δ) ^ (t / m)
        * tvDistance (ν ᵥ* P ^ (t % m)) π := hpair
    _ ≤ (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) * tvDistance ν π :=
        mul_le_mul_of_nonneg_left hrem (pow_nonneg hρnn _)

/-! ### The Dobrushin coefficient and the sharp matrix-level TV
contraction (2026-09-02, `proposals/directed-uniform-mixing-time.md`)

The Doeblin floor engine above contracts at the entrywise coefficient
`1 - |V|δ`. This section adds the *sharp* matrix-level companion: the
Dobrushin coefficient `δ(Q) = max_{x,y} TV(Q_x, Q_y)` of an arbitrary
matrix, the contraction `TV(μ ᵥ* Q, ν ᵥ* Q) ≤ TV(μ, ν) · δ(Q)` at
equal masses only, and the generic power submultiplicativity
`δ(Q^(s+t)) ≤ δ(Q^s) · δ(Q^t)` for row-stochastic `Q` — LPW's
`d(s+t) ≤ d(s) d(t)` in its matrix home. The undirected uniform-mixing
delivery proved this mechanism bespoke at the walk matrix's powers (in
`Oversmoothing.lean`); the matrix-level form is consumable by every
chain on the shelf, and the directed uniform object is its first
consumer. The pairing core is promoted here from `Oversmoothing.lean`'s
private copy — that module's own promotion note anticipated a second
consumer. -/

omit [DecidableEq V] in
/-- **The pairing core**: a zero-mass functional `c` paired against any
function `g` is bounded by half its `ℓ¹` mass times the oscillation
bound `D` of `g`. The recentering at a minimum of `g` (which exists:
`V` is finite) is what makes the positive-part split valid; the naive
triangle route loses a factor of `2` exactly here. Sharp: at
`c = (1, −1)`, `g = (0, 1)` the bound is attained. -/
theorem abs_sum_mul_le_of_pairwise [Nonempty V] {c g : V → ℝ}
    {D : ℝ} (hD : ∀ z z', |g z - g z'| ≤ D) (hc : ∑ z, c z = 0) :
    |∑ z, c z * g z| ≤ ((∑ z, |c z|) / 2) * D := by
  obtain ⟨z₀, hz₀⟩ := Finite.exists_min (α := V) g
  have hm : ∀ z, 0 ≤ g z - g z₀ := fun z => sub_nonneg.2 (hz₀ z)
  have hD' : ∀ z, g z - g z₀ ≤ D := fun z =>
    le_trans (le_abs_self _) (hD z z₀)
  have hone : ∀ cc : V → ℝ, ∑ z, cc z = 0 →
      ∑ z, cc z * g z ≤ ((∑ z, |cc z|) / 2) * D := by
    intro cc hcc
    have hzero : ∑ z, cc z * g z₀ = 0 := by
      rw [← Finset.sum_mul, hcc]
      ring
    have hrc : ∑ z, cc z * g z = ∑ z, cc z * (g z - g z₀) := by
      have heq : ∑ z, cc z * (g z - g z₀)
          = ∑ z, cc z * g z - ∑ z, cc z * g z₀ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [heq, hzero, sub_zero]
    rw [hrc]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset V) (fun z => 0 < cc z)
      (fun z => cc z * (g z - g z₀))
    have hneg : ∑ z ∈ (Finset.univ : Finset V).filter (fun z => ¬ 0 < cc z),
          cc z * (g z - g z₀) ≤ 0 := by
      refine Finset.sum_nonpos fun z hz => ?_
      have hcz : cc z ≤ 0 := by simpa [Finset.mem_filter] using hz
      rw [mul_comm]
      exact mul_nonpos_of_nonneg_of_nonpos (hm z) hcz
    have hpossum : ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
          cc z = (∑ z, |cc z|) / 2 := by
      have hposabs : ∑ z ∈ (Finset.univ : Finset V).filter
            (fun z => 0 < cc z), |cc z|
          = ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z), cc z :=
          Finset.sum_congr rfl fun z hz =>
            abs_of_pos (by simpa [Finset.mem_filter] using hz)
      have hnegabs : ∑ z ∈ (Finset.univ : Finset V).filter
            (fun z => ¬ 0 < cc z), |cc z|
          = ∑ z ∈ (Finset.univ : Finset V).filter (fun z => ¬ 0 < cc z),
              (-cc z) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        have hcz : cc z ≤ 0 := by simpa [Finset.mem_filter] using hz
        rw [abs_of_nonpos hcz]
      have hsum := Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset V) (fun z => 0 < cc z) (fun z => |cc z|)
      have huniv : ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
            cc z + ∑ z ∈ (Finset.univ : Finset V).filter
              (fun z => ¬ 0 < cc z), cc z = 0 := by
        rw [Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset V) (fun z => 0 < cc z) cc]
        exact hcc
      have hnegsum : ∑ z ∈ (Finset.univ : Finset V).filter
            (fun z => ¬ 0 < cc z), (-cc z)
          = ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
              cc z := by
        rw [Finset.sum_neg_distrib]
        have hpair : ∑ z ∈ (Finset.univ : Finset V).filter
              (fun z => ¬ 0 < cc z), cc z
            = -∑ z ∈ (Finset.univ : Finset V).filter
                (fun z => 0 < cc z), cc z := by linarith [huniv]
        rw [hpair]
        exact neg_neg _
      rw [← hsum, hposabs, hnegabs, hnegsum]
      ring
    have hle : ∑ z, cc z * (g z - g z₀)
        ≤ ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
          cc z * (g z - g z₀) := by linarith [hsplit, hneg]
    calc ∑ z, cc z * (g z - g z₀)
        ≤ ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
              cc z * (g z - g z₀) := hle
      _ ≤ ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
              cc z * D :=
          Finset.sum_le_sum fun z hz =>
            mul_le_mul_of_nonneg_left (hD' z)
              (le_of_lt (by simpa [Finset.mem_filter] using hz : 0 < cc z))
      _ = (∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
              cc z) * D := by
          rw [← Finset.sum_mul]
      _ = ((∑ z, |cc z|) / 2) * D := by rw [hpossum]
  have hmain := hone c hc
  have hnegc : ∑ z, (-c z) = 0 := by
    rw [Finset.sum_neg_distrib, hc, neg_zero]
  have hmain' := hone (-c) hnegc
  have habsneg : ∑ z, |(-c) z| = ∑ z, |c z| :=
    Finset.sum_congr rfl fun z _ => abs_neg _
  rw [habsneg] at hmain'
  have hval : ∑ z, (-c z) * g z = -∑ z, c z * g z := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  simp only [Pi.neg_apply] at hmain'
  rw [hval] at hmain'
  exact abs_le.2 ⟨by linarith, hmain⟩

omit [DecidableEq V] in
/-- **The Dobrushin coefficient of a matrix**: the worst-case
total-variation distance between two of its rows,
`δ(Q) = max_{x,y} TV(Q_x, Q_y)` — the contraction coefficient of the
classical Dobrushin ergodicity argument, at its matrix level (no
stochasticity in the definition; on a finite type the sup is a genuine
maximum). At a row-stochastic `Q` this is LPW's two-start distance
`d(1)` of the chain `Q` drives. -/
noncomputable def tvDobrushinCoeff (Q : Matrix V V ℝ) [Nonempty V] : ℝ :=
  (Finset.univ : Finset (V × V)).sup'
    ⟨(‹Nonempty V›.some, ‹Nonempty V›.some), Finset.mem_univ _⟩ fun p =>
      tvDistance (Q p.1) (Q p.2)

omit [DecidableEq V] in
theorem tvDobrushinCoeff_nonneg (Q : Matrix V V ℝ) [Nonempty V] :
    0 ≤ tvDobrushinCoeff Q :=
  le_trans (tvDistance_nonneg _ _)
    (Finset.le_sup'
      (f := fun p : V × V => tvDistance (Q p.1) (Q p.2))
      (Finset.mem_univ (‹Nonempty V›.some, ‹Nonempty V›.some)))

omit [DecidableEq V] in
/-- **The sharp Dobrushin contraction, matrix level**: applying a
matrix `Q` to both sides of an equal-mass pair of vectors contracts
their TV distance by the Dobrushin coefficient of `Q` —
`TV(μ ᵥ* Q, ν ᵥ* Q) ≤ TV(μ, ν) · δ(Q)`. Hypothesis-minimal: no
stochasticity, no signs, only equal masses. Proof: the sign statistic
of the evolved difference, transported to a pairing against the row
statistics `z ↦ Q_z ⬝ᵥ s`, whose oscillation is bounded by `2 δ(Q)`
through the distinguishing-function bound (`|s| ≤ 1`), closed by the
pairing core. The undirected uniform-mixing delivery proved this
mechanism bespoke at the walk matrix's powers
(`tvDistance_pow_walkTransitionMatrixTranspose_mulVec_le`); this is
the same engine at the matrix level, consumable by every chain on the
shelf (undirected, lazy, directed — any row action). The constant is
sharp: QA pins it attained exactly at the basis pair on the Google
fixture (`PRU_contraction_attained_QA`).

QA: exercised by `Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`
(Section H). -/
theorem tvDistance_vecMul_le_tvDobrushinCoeff [Nonempty V]
    {Q : Matrix V V ℝ} (μ ν : V → ℝ)
    (hmass : ∑ i, μ i = ∑ i, ν i) :
    tvDistance (μ ᵥ* Q) (ν ᵥ* Q)
      ≤ tvDistance μ ν * tvDobrushinCoeff Q := by
  have hmass0 : ∑ z, (μ - ν) z = 0 := by
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  set s : V → ℝ :=
    fun w => if 0 ≤ ((μ - ν) ᵥ* Q) w then 1 else -1 with hsdef
  have hsabs : ∀ w, |s w| ≤ 1 := by
    intro w
    by_cases h : 0 ≤ ((μ - ν) ᵥ* Q) w
    · simp only [hsdef, if_pos h]
      norm_num
    · simp only [hsdef, if_neg h]
      norm_num
  have hsval : ∀ w, s w * ((μ - ν) ᵥ* Q) w
      = |((μ - ν) ᵥ* Q) w| := by
    intro w
    by_cases h : 0 ≤ ((μ - ν) ᵥ* Q) w
    · simp only [hsdef, if_pos h, abs_of_nonneg h]
      ring
    · simp only [hsdef, if_neg h, abs_of_neg (lt_of_not_ge h)]
      ring
  have hosc : ∀ z z' : V,
      |(∑ w, Q z w * s w) - ∑ w, Q z' w * s w|
        ≤ 2 * tvDobrushinCoeff Q := by
    intro z z'
    have hgg : (∑ w, Q z w * s w) - ∑ w, Q z' w * s w
        = ∑ w, (Q z w - Q z' w) * s w := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hd := tvDistance_ge_half_abs_sum
      (μ := fun j => Q z j) (ν := fun j => Q z' j) s hsabs
    rw [hgg]
    have hsup : tvDistance (fun j => Q z j) (fun j => Q z' j)
        ≤ tvDobrushinCoeff Q :=
      Finset.le_sup'
        (f := fun p : V × V => tvDistance (Q p.1) (Q p.2))
        (Finset.mem_univ (z, z'))
    calc |∑ w, (Q z w - Q z' w) * s w|
        ≤ 2 * tvDistance (fun j => Q z j) (fun j => Q z' j) := by linarith
      _ ≤ 2 * tvDobrushinCoeff Q := mul_le_mul_of_nonneg_left hsup (by norm_num)
  have hpairing : ∑ w, |((μ - ν) ᵥ* Q) w|
      = ∑ z, (μ - ν) z * (∑ w, Q z w * s w) := by
    calc ∑ w, |((μ - ν) ᵥ* Q) w|
        = ∑ w, s w * ((μ - ν) ᵥ* Q) w :=
          Finset.sum_congr rfl fun w _ => (hsval w).symm
      _ = ∑ w, ∑ z, (μ - ν) z * (Q z w * s w) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          simp only [Matrix.vecMul, Matrix.dotProduct]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ = ∑ z, ∑ w, (μ - ν) z * (Q z w * s w) := Finset.sum_comm
      _ = ∑ z, (μ - ν) z * (∑ w, Q z w * s w) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum]
  have hp := abs_sum_mul_le_of_pairwise (c := μ - ν)
    (g := fun z => ∑ w, Q z w * s w) hosc hmass0
  have hL1 : ∑ z, |(μ - ν) z| = 2 * tvDistance μ ν := by
    simp only [Pi.sub_apply, tvDistance]
    ring
  have hsplit : ∀ w : V, (μ ᵥ* Q) w - (ν ᵥ* Q) w = ((μ - ν) ᵥ* Q) w := by
    intro w
    rw [← Pi.sub_apply, Matrix.sub_vecMul]
  calc tvDistance (μ ᵥ* Q) (ν ᵥ* Q)
      = (1 / 2) * ∑ w, |((μ - ν) ᵥ* Q) w| := by
          rw [tvDistance]
          congr 1
          exact Finset.sum_congr rfl fun w _ => by rw [hsplit w]
    _ = (1 / 2) * ∑ z, (μ - ν) z * (∑ w, Q z w * s w) := by
          rw [hpairing]
    _ ≤ (1 / 2) * |∑ z, (μ - ν) z * (∑ w, Q z w * s w)| := by
          exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ (1 / 2) * (((∑ z, |(μ - ν) z|) / 2) * (2 * tvDobrushinCoeff Q)) := by
          exact mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = tvDistance μ ν * tvDobrushinCoeff Q := by
          rw [hL1]
          ring

/-- **Generic submultiplicativity of the Dobrushin coefficient** for
row-stochastic powers: `δ(Q^(s+t)) ≤ δ(Q^s) · δ(Q^t)` — LPW's
`d(s+t) ≤ d(s) d(t)` in its matrix home, pure Markovity (row
stochasticity is the only hypothesis: it supplies the equal-mass
condition of the contraction along the power's rows). QA pins it
attained with equality at every time on the Google fixture
(`PRU_pair_submul_attained_QA`).

QA: exercised by `Scaffold.QA.SpectralGraph.DirectedMixing_QA.*`
(Section H). -/
theorem tvDobrushinCoeff_pow_add_le [Nonempty V] (Q : Matrix V V ℝ)
    (hrow : ∀ i, ∑ j, Q i j = 1) (s t : ℕ) :
    tvDobrushinCoeff (Q ^ (s + t))
      ≤ tvDobrushinCoeff (Q ^ s) * tvDobrushinCoeff (Q ^ t) := by
  have hrowid : ∀ x : V, (Q ^ (s + t)) x = ((Q ^ s) x) ᵥ* (Q ^ t) := by
    intro x
    funext j
    simp only [Matrix.vecMul, Matrix.dotProduct, Matrix.mul_apply, pow_add]
  refine Finset.sup'_le
    (⟨(‹Nonempty V›.some, ‹Nonempty V›.some), Finset.mem_univ _⟩ :
      (Finset.univ : Finset (V × V)).Nonempty)
    (f := fun p : V × V =>
      tvDistance ((Q ^ (s + t)) p.1) ((Q ^ (s + t)) p.2))
    fun p _ => ?_
  show tvDistance ((Q ^ (s + t)) p.1) ((Q ^ (s + t)) p.2)
    ≤ tvDobrushinCoeff (Q ^ s) * tvDobrushinCoeff (Q ^ t)
  rw [hrowid p.1, hrowid p.2]
  have hmass : ∑ i, (Q ^ s) p.1 i = ∑ i, (Q ^ s) p.2 i := by
    rw [pow_row_sum hrow s p.1, pow_row_sum hrow s p.2]
  calc tvDistance (((Q ^ s) p.1) ᵥ* (Q ^ t)) (((Q ^ s) p.2) ᵥ* (Q ^ t))
      ≤ tvDistance ((Q ^ s) p.1) ((Q ^ s) p.2) * tvDobrushinCoeff (Q ^ t) :=
        tvDistance_vecMul_le_tvDobrushinCoeff _ _ hmass
    _ ≤ tvDobrushinCoeff (Q ^ s) * tvDobrushinCoeff (Q ^ t) := by
        refine mul_le_mul_of_nonneg_right ?_ (tvDobrushinCoeff_nonneg (Q ^ t))
        exact Finset.le_sup'
          (f := fun p : V × V => tvDistance ((Q ^ s) p.1) ((Q ^ s) p.2))
          (Finset.mem_univ p)

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

/-!
### The primitivity supplier at the walk, the Doeblin rate, and the
convergence corollary (2026-09-02,
`proposals/primitivity-supplier-plain-walk.md`)

The standing handoff's named blocker delivered: on a connected support
graph containing a single odd closed walk, the walk transition matrix
is primitive — `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk`
(reversal handled at the `Walk` level, since `P = D⁻¹A` is not
symmetric on irregular graphs; `Odd p.length` is the honest interface,
the pinned Mathlib having no `SimpleGraph.Bipartite`). Two consumers:
`walkDistribution_tvDistance_le_of_pos_power` — the plain walk's first
mixing rate with no spectral certificate and no caller-supplied `r`
(the intrinsic-rate family's non-bipartite member), and
`walkDistribution_tendsto_stationaryVec` — the retired
`primitive_power_tendsto`'s first undirected consumer. All proved,
zero axioms.
-/

open Filter Topology

/-- **The walk-to-power bridge**: every support-graph walk of length `t`
from `i` to `j` gives a strictly positive `(i, j)` entry of the `t`-th
power of the walk transition matrix. Induction over
`SimpleGraph.Walk`; each adjacency step contributes one positive
product term `(P^s) i k · P k l` of the defining sum. -/
theorem pow_walkTransitionMatrix_pos_of_walk (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    {i j : V} (w : (supportGraph A hA).Walk i j) :
    0 < (walkTransitionMatrix A ^ w.length) i j := by
  induction w with
  | nil =>
    simp [Matrix.one_apply, SimpleGraph.Walk.length_nil]
  | @cons u k v hadj rest ih =>
    rw [SimpleGraph.Walk.length_cons]
    have hcomb : 0 < (walkTransitionMatrix A ^ (1 + rest.length)) u v := by
      have hedge : 0 < (walkTransitionMatrix A ^ 1) u k := by
        rw [pow_one, walkTransitionMatrix_apply]
        exact mul_pos (inv_pos.mpr (hd u)) ((supportGraph_adj.1 hadj).2)
      exact Scaffold.LinearAlgebra.pow_entry_pos_of_pos
        (fun a b => walkTransitionMatrix_nonneg A hnn hd a b) hedge ih
    exact (Nat.add_comm 1 rest.length) ▸ hcomb

/-- **The walk-level primitivity supplier** — the standing handoff's
named blocker: on a connected support graph containing a single odd
closed walk, the walk transition matrix is primitive. Connectivity
supplies the reachability witnesses through the walk-to-power bridge;
positive degrees supply the positive 2-cycles (a positive row sum of
nonnegative entries has a positive entry, both directions along the
symmetric `A`); and the odd closed walk at *one* vertex transports to
every vertex by concatenating a walk there, the odd walk, and the
*reversed* walk back — total length `2·|q| + |p|`, odd. The reversal
must live here, at the `Walk` level: `walkTransitionMatrix` is not
symmetric on irregular graphs. `Odd p.length` is the honest interface —
the pinned Mathlib has no `SimpleGraph.Bipartite` to state
"non-bipartite" through. -/
theorem walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i)
    (hconn : (supportGraph A hA).Connected)
    {w : V} (p : (supportGraph A hA).Walk w w) (hp : Odd p.length) :
    (walkTransitionMatrix A).IsPrimitive := by
  refine Scaffold.LinearAlgebra.isPrimitive_of_pow_pos_of_odd_loop
    (fun a b => walkTransitionMatrix_nonneg A hnn hd a b) ?_ ?_ ?_
  · intro u v
    obtain ⟨q⟩ := hconn.1 u v
    exact ⟨q.length, pow_walkTransitionMatrix_pos_of_walk A hA hnn hd q⟩
  · intro v
    obtain ⟨z, hz⟩ : ∃ z, 0 < A v z := by
      by_contra hcon
      push_neg at hcon
      have h0 : deg A v = 0 := by
        simp only [deg]
        exact Finset.sum_eq_zero fun j _ => le_antisymm (hcon j) (hnn v j)
      have hv := hd v
      rw [h0] at hv
      exact absurd hv (by norm_num)
    have hzv : 0 < A z v := by
      have hzs := hz
      rwa [hA.apply z v] at hzs
    refine ⟨z, ?_, ?_⟩
    · rw [walkTransitionMatrix_apply]
      exact mul_pos (inv_pos.mpr (hd v)) hz
    · rw [walkTransitionMatrix_apply]
      exact mul_pos (inv_pos.mpr (hd z)) hzv
  · intro v
    obtain ⟨q⟩ := hconn.1 v w
    have hq : 0 < (walkTransitionMatrix A ^ q.length) v w :=
      pow_walkTransitionMatrix_pos_of_walk A hA hnn hd q
    have hqr : 0 < (walkTransitionMatrix A ^ q.length) w v := by
      rw [← SimpleGraph.Walk.length_reverse q]
      exact pow_walkTransitionMatrix_pos_of_walk A hA hnn hd q.reverse
    have hloop : 0 < (walkTransitionMatrix A ^ p.length) w w :=
      pow_walkTransitionMatrix_pos_of_walk A hA hnn hd p
    obtain ⟨k, hk⟩ := hp
    refine ⟨q.length + (p.length + q.length), ⟨q.length + k, by rw [hk]; omega⟩, ?_⟩
    have hs1 := Scaffold.LinearAlgebra.pow_entry_pos_of_pos
      (a := q.length) (b := p.length)
      (fun a b => walkTransitionMatrix_nonneg A hnn hd a b) hq hloop
    have hfin := Scaffold.LinearAlgebra.pow_entry_pos_of_pos
      (a := q.length + p.length) (b := q.length)
      (fun a b => walkTransitionMatrix_nonneg A hnn hd a b) hs1 hqr
    rwa [Nat.add_assoc] at hfin

/-! ### The Doeblin rate at the produced positive power -/


/-- **The plain walk's Doeblin rate**: at a strictly-positive-power
certificate `δ ≤ (P^m) i j`, the walk law's TV distance to stationarity
is at most `(1 − |V|δ)^(t/m)` — with `TV(δ_x, π) ≤ 1` folded in through
the simplex diameter. The plain walk's first mixing rate with no
spectral certificate and no caller-supplied `r`: the intrinsic-rate
family's non-bipartite member (the entrywise lazy ceiling being its
bipartite member), consuming the same engine as the directed PageRank
rate. -/
theorem walkDistribution_tvDistance_le_of_pos_power (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] {m : ℕ} {δ : ℝ}
    (hle : ∀ i j, δ ≤ (walkTransitionMatrix A ^ m) i j)
    (t : ℕ) (x : V) :
    tvDistance (walkDistribution A t x) (stationaryVec A)
      ≤ (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) := by
  have hPnn : ∀ i j, 0 ≤ walkTransitionMatrix A i j :=
    walkTransitionMatrix_nonneg A hnn hd
  have hProw : ∀ i, ∑ j, walkTransitionMatrix A i j = 1 :=
    walkTransitionMatrix_row_sum A hd
  have hπstat : stationaryVec A ᵥ* walkTransitionMatrix A
      = stationaryVec A := by
    rw [← Matrix.mulVec_transpose]
    exact walk_isStationary A hA hd
  have hlaw : walkDistribution A t x
      = (Pi.single x (1 : ℝ)) ᵥ* (walkTransitionMatrix A ^ t) := by
    rw [walkDistribution, ← Matrix.transpose_pow, ← Matrix.mulVec_transpose]
  have hνsum : ∑ i, (Pi.single x (1 : ℝ)) i = 1 := by
    simp [Pi.single_apply]
  have hρ : 0 ≤ 1 - (Fintype.card V : ℝ) * δ := by
    obtain ⟨i₀⟩ := ‹Nonempty V›
    have h1 : (Fintype.card V : ℝ) * δ ≤ 1 := by
      calc (Fintype.card V : ℝ) * δ = ∑ j : V, δ := by simp
        _ ≤ ∑ j, (walkTransitionMatrix A ^ m) i₀ j :=
            Finset.sum_le_sum fun j _ => hle i₀ j
        _ = 1 := Scaffold.LinearAlgebra.pow_row_sum hProw m i₀
    linarith
  have hmain := tvDistance_vecMul_pow_le_of_pos_power hPnn hProw hle
    (sum_stationaryVec A hd) hπstat hνsum t
  calc tvDistance (walkDistribution A t x) (stationaryVec A)
      = tvDistance ((Pi.single x (1 : ℝ)) ᵥ* (walkTransitionMatrix A ^ t))
          (stationaryVec A) := by rw [hlaw]
    _ ≤ (1 - (Fintype.card V : ℝ) * δ) ^ (t / m)
        * tvDistance (Pi.single x (1 : ℝ)) (stationaryVec A) := hmain
    _ ≤ (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hρ _)
        exact tvDistance_le_one_of_nonneg_of_sum_eq_one
          (fun i => by
            by_cases hi : i = x <;> simp [Pi.single_apply, hi])
          hνsum
          (fun i => le_of_lt (stationaryVec_pos A hd i))
          (sum_stationaryVec A hd)
    _ = (1 - (Fintype.card V : ℝ) * δ) ^ (t / m) := mul_one _

/-- **The retired `primitive_power_tendsto`'s first undirected
consumer**: on the supplier's hypothesis set, the plain walk law
converges to stationarity — the classical finite-Markov-chain
convergence theorem on every connected graph with an odd closed walk,
composed from the proved `primitive_vecMul_tendsto` through the
law/power bridge. -/
theorem walkDistribution_tendsto_stationaryVec (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hconn : (supportGraph A hA).Connected)
    {w : V} (p : (supportGraph A hA).Walk w w) (hp : Odd p.length)
    (x : V) :
    Filter.Tendsto (fun t : ℕ => walkDistribution A t x) Filter.atTop
      (𝓝 (stationaryVec A)) := by
  have hprim := walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk
    A hA hnn hd hconn p hp
  have hPnn : ∀ i j, 0 ≤ walkTransitionMatrix A i j :=
    walkTransitionMatrix_nonneg A hnn hd
  have hProw : ∀ i, ∑ j, walkTransitionMatrix A i j = 1 :=
    walkTransitionMatrix_row_sum A hd
  have hπstat : stationaryVec A ᵥ* walkTransitionMatrix A
      = stationaryVec A := by
    rw [← Matrix.mulVec_transpose]
    exact walk_isStationary A hA hd
  have hνsum : ∑ i, (Pi.single x (1 : ℝ)) i = 1 := by
    simp [Pi.single_apply]
  have hmain := Scaffold.LinearAlgebra.primitive_vecMul_tendsto
    (walkTransitionMatrix A) hPnn
    hProw hprim (fun i => le_of_lt (stationaryVec_pos A hd i))
    (sum_stationaryVec A hd) hπstat (Pi.single x (1 : ℝ)) hνsum
  have hlaw : ∀ t : ℕ, (Pi.single x (1 : ℝ)) ᵥ* (walkTransitionMatrix A ^ t)
      = walkDistribution A t x := by
    intro t
    rw [walkDistribution, ← Matrix.transpose_pow, ← Matrix.mulVec_transpose]
  exact hmain.congr hlaw

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

open Scaffold.InformationTheory

/-! ## The entropy leg of the mixing program

`proposals/entropy-mixing-pinsker.md` (2026-09-01): Pinsker's
inequality in the shelf's vector TV form, the entropy–χ² bridge's
walk-level decay family (discrete certificate form + continuous-time
intrinsic-rate twin), and the nonnegativity plumbing the continuous
twin needs. Every declaration here is proved hard crust — zero
axioms; the binary two-point engine lives in
`InformationTheory.Entropy`.
-/

/-! ## The entropy leg: nonnegativity plumbing -/

/-- The walk density is entrywise nonnegative: the walk law is
nonnegative and `π` is strictly positive. -/
theorem walkDensity_nonneg (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x i : V) :
    0 ≤ walkDensity A t x i :=
  div_nonneg (walkDistribution_nonneg A hnn hd t x i)
    (le_of_lt (stationaryVec_pos A hd i))

/-- The continuous-time walk density is entrywise nonnegative at
nonnegative times: the Poissonization identity exhibits it as a series
of nonneg scalars times nonneg discrete densities (`tsum_nonneg`). -/
theorem contWalkDensity_nonneg (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i) [Nonempty V]
    {t : ℝ} (ht : 0 ≤ t) (x i : V) :
    0 ≤ contWalkDensity A t x i := by
  have hpi := (Pi.hasSum.mp (hasSum_poisson_walkDensity A hA hd t x)) i
  have hdc : contWalkDensity A t x i
      = (walkHeatKernel A t *ᵥ walkDensity A 0 x) i := rfl
  rw [hdc]
  rw [← hpi.tsum_eq]
  refine tsum_nonneg fun k => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (poissonWeight_nonneg ht k)
    (walkDensity_nonneg A hnn hd k x i)

/-- The continuous-time walk law is entrywise nonnegative: `π ≥ 0`
weights a nonnegative density. -/
theorem contWalkDistribution_nonneg (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] {t : ℝ} (ht : 0 ≤ t) (x i : V) :
    0 ≤ contWalkDistribution A t x i := by
  simp only [contWalkDistribution]
  exact mul_nonneg (le_of_lt (stationaryVec_pos A hd i))
    (contWalkDensity_nonneg A hA hnn hd ht x i)

/-- The continuous-time walk law is a probability vector: `∑ π h = 1`,
the `contWalkDistribution` packaging of the shelf's mass conservation. -/
theorem sum_contWalkDistribution (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℝ) (x : V) :
    ∑ i, contWalkDistribution A t x i = 1 := by
  simp only [contWalkDistribution]
  exact sum_stationaryVec_contWalkDensity A hA hd t x

/-! ## Pinsker's inequality and the decay/floor theorems -/

/-- **Pinsker's inequality** in the shelf's vector TV form: the
total-variation distance between a probability vector and a strictly
positive one is at most the square root of half the relative entropy.
Assembly: the TV-as-positive-part identity (`TV = ∑_{q<p}(p−q) = a − b`
at `a = p(S)`, `b = q(S)` for `S = {q < p}`), the two-block
decomposition of `klDiv` through the two-block log-sum bound, and the
binary two-point bound. The strict `0 < q i` hypothesis is
load-bearing: at `q = (1, 0)` the junk `klTerm (1/2) 0 = 0` makes the
un-guarded statement read `1/2 ≤ (1/2)·|log (1/2)|`-scale falsities
(refuted in QA). -/
theorem tvDistance_le_sqrt_half_klDiv {p q : V → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq : ∀ i, 0 < q i) (hq1 : ∑ i, q i = 1) :
    tvDistance p q ≤ Real.sqrt (klDiv p q / 2) := by
  classical
  set S : Finset V := Finset.univ.filter fun i => q i < p i with hSdef
  have hmem : ∀ i : V, i ∈ S ↔ q i < p i := by
    intro i
    simp [hSdef, Finset.mem_filter]
  have hScard : ∀ (f : V → ℝ), ∑ i in S, f i + ∑ i in Sᶜ, f i = ∑ i, f i :=
    fun f => Finset.sum_add_sum_compl S f
  rcases S.eq_empty_or_nonempty with hSe | hSn
  · -- S = ∅: p ≤ q pointwise with equal mass forces p = q
    have hle : ∀ i : V, p i ≤ q i := by
      intro i
      by_contra hcon
      push_neg at hcon
      exact absurd ((hmem i).mpr hcon) (by
        intro hm
        rw [hSe] at hm
        simp at hm)
    have hsub : ∀ i : V, (0:ℝ) ≤ q i - p i := fun i => sub_nonneg.mpr (hle i)
    have hsum0 : ∑ i, (q i - p i) = 0 := by
      rw [Finset.sum_sub_distrib, hq1, hp1, sub_self]
    have hqpe : ∀ i : V, q i - p i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => hsub j)).mp hsum0 i (Finset.mem_univ i)
    have hpe : p = q := by
      funext i
      have := hqpe i
      linarith [this]
    have hTV0 : tvDistance p q = 0 := by
      rw [hpe]
      simp [tvDistance]
    rw [hTV0]
    positivity
  · -- S nonempty: TV = a − b, klDiv ≥ 2(a−b)²
    obtain ⟨a, ha⟩ : ∃ a, ∑ i in S, p i = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, ∑ i in S, q i = b := ⟨_, rfl⟩
    obtain ⟨i₀, hi₀⟩ := hSn
    have hb0 : (0:ℝ) < b := by
      rw [← hb]
      exact Finset.sum_pos' (fun i _ => le_of_lt (hq i)) ⟨i₀, hi₀, hq i₀⟩
    have hSne : S ≠ Finset.univ := by
      intro hSu
      have hle : ∀ i ∈ (Finset.univ : Finset V), q i ≤ p i :=
        fun i _ =>
          le_of_lt ((hmem i).mp (by rw [hSu]; exact Finset.mem_univ i))
      have hstrict : ∃ i ∈ (Finset.univ : Finset V), q i < p i :=
        ⟨i₀, Finset.mem_univ i₀,
          (hmem i₀).mp (by rw [hSu]; exact Finset.mem_univ i₀)⟩
      have hlt := Finset.sum_lt_sum hle hstrict
      rw [hq1, hp1] at hlt
      exact absurd hlt (by norm_num)
    have hcompne : (Sᶜ).Nonempty := by
      rcases Finset.eq_empty_or_nonempty Sᶜ with hc | hc
      · exfalso
        refine hSne (Finset.eq_univ_of_forall fun i => ?_)
        by_contra hcon
        exact absurd (Finset.mem_compl.mpr hcon) (by
          rw [hc]
          simp)
      · exact hc
    have hcp : ∑ i in Sᶜ, p i = 1 - a := by
      have h2 := hScard p
      rw [ha, hp1] at h2
      linarith
    have hcq : ∑ i in Sᶜ, q i = 1 - b := by
      have h2 := hScard q
      rw [hb, hq1] at h2
      linarith
    have hb1 : b < 1 := by
      obtain ⟨j₀, hj₀⟩ := hcompne
      have hpos : (0:ℝ) < ∑ i in Sᶜ, q i :=
        Finset.sum_pos' (fun i _ => le_of_lt (hq i)) ⟨j₀, hj₀, hq j₀⟩
      rw [hcq] at hpos
      linarith
    -- TV = a − b
    have honS : ∀ i ∈ S, |p i - q i| = p i - q i := fun i hi =>
      abs_of_pos (sub_pos.2 ((hmem i).mp hi))
    have honC : ∀ i ∈ Sᶜ, |p i - q i| = q i - p i := by
      intro i hi
      have hle : p i ≤ q i :=
        le_of_not_gt fun h => (Finset.mem_compl.mp hi) ((hmem i).mpr h)
      exact (abs_of_nonpos (sub_nonpos.mpr hle)).trans (by ring)
    have hab0 : (0:ℝ) ≤ a - b := by
      have h2 : (0:ℝ) ≤ ∑ i in S, (p i - q i) :=
        Finset.sum_nonneg fun i (hi : i ∈ S) =>
          sub_nonneg.mpr (le_of_lt ((hmem i).mp hi))
      rw [Finset.sum_sub_distrib, ha, hb] at h2
      linarith
    have hTV : tvDistance p q = a - b := by
      have hsumS : ∑ i in S, (p i - q i) = a - b := by
        rw [Finset.sum_sub_distrib, ha, hb]
      have hsumC : ∑ i in Sᶜ, (q i - p i) = a - b := by
        rw [Finset.sum_sub_distrib, hcq, hcp]
        ring
      have e1 : ∑ i in S, |p i - q i| = ∑ i in S, (p i - q i) :=
        Finset.sum_congr rfl fun i hi => honS i hi
      have e2 : ∑ i in Sᶜ, |p i - q i| = ∑ i in Sᶜ, (q i - p i) :=
        Finset.sum_congr rfl fun i hi => honC i hi
      have hsplit : ∑ i, |p i - q i|
          = (∑ i in S, (p i - q i)) + ∑ i in Sᶜ, (q i - p i) := by
        rw [(hScard fun i => |p i - q i|).symm, e1, e2]
      rw [tvDistance, hsplit, hsumS, hsumC]
      linarith
    -- klDiv ≥ 2 (a − b)²
    have hkl1 := sum_klTerm_ge_klTerm S hp hq
    have hkl2 := sum_klTerm_ge_klTerm Sᶜ hp hq
    rw [hcp] at hkl2
    rw [hcq] at hkl2
    have hsplitK : klDiv p q
        = (∑ i in S, klTerm (p i) (q i)) + ∑ i in Sᶜ, klTerm (p i) (q i) :=
      (hScard fun i => klTerm (p i) (q i)).symm
    have ha1 : (0:ℝ) ≤ a := by
      rw [← ha]
      exact Finset.sum_nonneg fun i _ => hp i
    have ha2 : a ≤ 1 := by
      have h2 := hScard p
      rw [hp1] at h2
      have hcomp : (0:ℝ) ≤ ∑ i in Sᶜ, p i :=
        Finset.sum_nonneg fun i _ => hp i
      rw [ha] at h2
      linarith
    have hbin := klTerm_add_klTerm_one_sub_ge_two_sq ha1 ha2 hb0 hb1
    have hS' : klTerm a b ≤ ∑ i in S, klTerm (p i) (q i) := by
      rw [← ha, ← hb]
      exact hkl1
    have hge : 2 * (a - b) ^ 2 ≤ klDiv p q := by
      rw [hsplitK]
      linarith [hbin, hS', hkl2]
    -- finish
    rw [hTV, ← Real.sqrt_sq hab0]
    refine Real.sqrt_le_sqrt ?_
    linarith [hge]

/-- **Entropy decay along the walk**: the relative entropy of the walk
law from the stationary distribution is at most `r^{2t}·((πx)⁻¹−1)` at
exactly the χ² mixing bound's hypothesis set — the bridge composed
with the delivered `chiSquareDistance_le_of_connected`. Entropy decays
at the χ² rate because `D ≤ χ²` termwise. -/
theorem klDiv_walkDistribution_le (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hconn : (supportGraph A hA).Connected) (r : ℝ) (t : ℕ) (x : V)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r) :
    klDiv (walkDistribution A t x) (stationaryVec A)
      ≤ r ^ (2 * t) * ((stationaryVec A x)⁻¹ - 1) :=
  (klDiv_le_sum_sq_div (walkDistribution_nonneg A hnn hd t x)
    (fun i => stationaryVec_pos A hd i)
    (sum_walkDistribution A hd t x) (sum_stationaryVec A hd)).trans
    (chiSquareDistance_le_of_connected A hA hnn hd hconn r t x hrate)

/-- **Entropy decay, continuous-time twin**: at exactly
`contChiSquareDistance_le`'s hypothesis set, `D ≤ e^{−2tλ₂(L_sym)}·
((πx)⁻¹−1)` — the intrinsic-rate version, no caller certificate. -/
theorem klDiv_contWalkDistribution_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hcard : 2 ≤ Fintype.card V) {t : ℝ} (ht : 0 ≤ t)
    (x : V) :
    klDiv (contWalkDistribution A t x) (stationaryVec A)
      ≤ Real.exp (-(2 * t * secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard))
        * ((stationaryVec A x)⁻¹ - 1) := by
  have h1 : klDiv (contWalkDistribution A t x) (stationaryVec A)
      ≤ ∑ i, (contWalkDistribution A t x i - stationaryVec A i)^2
          / stationaryVec A i :=
    klDiv_le_sum_sq_div (fun i => contWalkDistribution_nonneg A hA hnn hd ht x i)
      (fun i => stationaryVec_pos A hd i)
      (sum_contWalkDistribution A hA hd t x) (sum_stationaryVec A hd)
  rw [← contChiSquareDistance_eq_sum_div A hd t x] at h1
  exact h1.trans (contChiSquareDistance_le A hA hnn hd hcard ht x)


/-!
## The lazy walk — the discrete mixing program's periodicity fix

`proposals/lazy-walk-mixing.md` (2026-09-01): the lazy walk operator
`P_L = (P + 1)/2` (Levin–Peres–Wilmer ch. 5's canonical convention for
discrete-time mixing) with its law, density, and χ² distance; the
signless-Laplacian sum-of-squares engine bounding the normalized
spectrum above by `2`; the lazy decay engine (conjugation, eigencoordinate
evolution, Parseval, ℓ²(π) contraction) at mode factors `1 − μ/2`; and
the headline `lazyChiSquareDistance_le_of_connected` — the χ² mixing
bound at the *intrinsic* rate `1 − λ₂(L_sym)/2` with connectivity the
only graph hypothesis, the continuous family's recorded advantage
delivered on the discrete side. On bipartite graphs (every path, tree,
even cycle), where the plain family's rate hypothesis is provably
unsatisfiable (`λ_max = 2` mode, factor `|1 − 2| = 1`), the lazy rate
still contracts. TV and entropy corollaries at the same rate.
-/

/-! ## The lazy walk operator and its law -/

/-- **The lazy walk transition matrix** `P_L = (P + 1)/2` —
Levin–Peres–Wilmer ch. 5's canonical convention for discrete-time
mixing (stay or move, probability `1/2` each). The operator whose mode
factors `1 − λ/2` lie in `[0, 1]`, exactly the property the plain walk
lacks on bipartite graphs (`|1 − 2| = 1`). Noncomputable because
`walkTransitionMatrix` is. -/
noncomputable def lazyWalkTransitionMatrix (A : WAdj (V := V)) :
    Matrix V V ℝ :=
  (2 : ℝ)⁻¹ • (walkTransitionMatrix A + 1)

/-- Entry form: `P_L i j = 2⁻¹ * (P i j + δ i j)` — the entry-level
interface the raw QA computations consume. -/
theorem lazyWalkTransitionMatrix_apply (A : WAdj (V := V)) (i j : V) :
    lazyWalkTransitionMatrix A i j
      = (2 : ℝ)⁻¹ * (walkTransitionMatrix A i j
          + (if i = j then 1 else 0)) := by
  simp [lazyWalkTransitionMatrix, Matrix.one_apply]

/-- The constant fix, lazy form: `P_L *ᵥ 1 = 1` (the average of two
row-stochastic operators is row-stochastic). -/
theorem lazyWalkTransitionMatrix_mulVec_one (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    lazyWalkTransitionMatrix A *ᵥ (1 : V → ℝ) = 1 := by
  have hP : walkTransitionMatrix A *ᵥ (1 : V → ℝ) = 1 :=
    walkTransitionMatrix_mulVec_one A hd
  have h1 : (1 : Matrix V V ℝ) *ᵥ (1 : V → ℝ) = 1 := by simp
  calc lazyWalkTransitionMatrix A *ᵥ (1 : V → ℝ)
      = (2 : ℝ)⁻¹ • (walkTransitionMatrix A *ᵥ (1 : V → ℝ)
          + (1 : Matrix V V ℝ) *ᵥ (1 : V → ℝ)) := by
            rw [lazyWalkTransitionMatrix, Matrix.smul_mulVec_assoc,
              Matrix.add_mulVec]
      _ = 1 := by
            rw [hP, h1]
            ext i
            have h2 : (2 : ℝ)⁻¹ * ((1 : ℝ) + 1) = 1 := by
              field_simp
            simpa [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using h2

/-- Entrywise nonnegativity of the lazy operator at nonnegative
weights and positive degrees. -/
theorem lazyWalkTransitionMatrix_nonneg (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i) (i j : V) :
    0 ≤ lazyWalkTransitionMatrix A i j := by
  have hP := walkTransitionMatrix_nonneg A hnn hd i j
  rw [lazyWalkTransitionMatrix_apply]
  rcases Decidable.em (i = j) with h | h
  · rw [if_pos h]
    exact mul_nonneg (by positivity) (by linarith)
  · rw [if_neg h, add_zero]
    exact mul_nonneg (by positivity) hP

/-- **The lazy walk law**: the distribution of the lazy walk started at
`x` after `t` steps, `(P_Lᵀ)ᵗ *ᵥ δₓ` — the plain object's exact
definition at the lazy operator. Noncomputable because
`lazyWalkTransitionMatrix` is. -/
noncomputable def lazyWalkDistribution (A : WAdj (V := V)) (t : ℕ)
    (x : V) : V → ℝ :=
  ((lazyWalkTransitionMatrix A)ᵀ ^ t) *ᵥ (Pi.single x (1 : ℝ))

/-- At time zero the lazy walk sits at its start. -/
theorem lazyWalkDistribution_zero (A : WAdj (V := V)) (x : V) :
    lazyWalkDistribution A 0 x = Pi.single x (1 : ℝ) := by
  simp only [lazyWalkDistribution]
  rw [pow_zero, Matrix.one_mulVec]

/-- The evolution equation: one more lazy step applies the adjoint lazy
operator to the current law. -/
theorem lazyWalkDistribution_succ (A : WAdj (V := V)) (t : ℕ) (x : V) :
    lazyWalkDistribution A (t + 1) x
      = (lazyWalkTransitionMatrix A)ᵀ *ᵥ lazyWalkDistribution A t x := by
  simp only [lazyWalkDistribution]
  rw [pow_succ', ← Matrix.mulVec_mulVec]

/-- Conservation of mass: the lazy walk's law is a probability vector
at every time (the average of two mass-preserving steps). -/
theorem sum_lazyWalkDistribution (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) (t : ℕ) (x : V) :
    ∑ i, lazyWalkDistribution A t x i = 1 := by
  have hstep : ∀ ν : V → ℝ,
      ∑ i, ((lazyWalkTransitionMatrix A)ᵀ *ᵥ ν) i = ∑ i, ν i := by
    intro ν
    have hexp : ∀ i : V, ((lazyWalkTransitionMatrix A)ᵀ *ᵥ ν) i
        = (2 : ℝ)⁻¹ * (((walkTransitionMatrix A)ᵀ *ᵥ ν) i + ν i) := by
      intro i
      have h1 : ((1 : Matrix V V ℝ) *ᵥ ν) i = ν i := by simp
      calc ((lazyWalkTransitionMatrix A)ᵀ *ᵥ ν) i
          = (((2 : ℝ)⁻¹ • ((walkTransitionMatrix A)ᵀ
              + (1 : Matrix V V ℝ))) *ᵥ ν) i := by
                rw [lazyWalkTransitionMatrix, Matrix.transpose_smul,
                  Matrix.transpose_add, Matrix.transpose_one]
          _ = ((2 : ℝ)⁻¹ • (((walkTransitionMatrix A)ᵀ *ᵥ ν
              + (1 : Matrix V V ℝ) *ᵥ ν))) i := by
                rw [Matrix.smul_mulVec_assoc, Matrix.add_mulVec]
          _ = (2 : ℝ)⁻¹ * (((walkTransitionMatrix A)ᵀ *ᵥ ν) i
              + ((1 : Matrix V V ℝ) *ᵥ ν) i) := by
                rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
          _ = (2 : ℝ)⁻¹ * (((walkTransitionMatrix A)ᵀ *ᵥ ν) i + ν i) := by
                rw [h1]
    have hplain : ∑ i, ((walkTransitionMatrix A)ᵀ *ᵥ ν) i = ∑ i, ν i := by
      simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, walkTransitionMatrix_row_sum A hd j, one_mul]
    rw [Finset.sum_congr rfl fun i _ => hexp i, ← Finset.mul_sum,
      Finset.sum_add_distrib, hplain]
    ring
  induction t with
  | zero =>
    rw [lazyWalkDistribution_zero]
    simp [Pi.single_apply]
  | succ t ih => rw [lazyWalkDistribution_succ, hstep, ih]

/-- Entrywise nonnegativity of the lazy walk law. -/
theorem lazyWalkDistribution_nonneg (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i) (t : ℕ) (x i : V) :
    0 ≤ lazyWalkDistribution A t x i := by
  have hall : ∀ j, 0 ≤ lazyWalkDistribution A t x j := by
    induction t with
    | zero =>
      intro j
      rw [lazyWalkDistribution_zero]
      rcases Decidable.em (j = x) with h | h <;> simp [Pi.single_apply, h]
    | succ t ih =>
      intro j
      rw [lazyWalkDistribution_succ]
      simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply]
      exact Finset.sum_nonneg fun k _ =>
        mul_nonneg (lazyWalkTransitionMatrix_nonneg A hnn hd k j) (ih k)
  exact hall i

/-- **Detailed balance, lazy form**: the stationary distribution
`π = deg/vol` is reversible for the lazy operator — the average of two
reversible-for-π operators (the identity trivially so). This is the
interface the lazy density evolution consumes. -/
theorem stationaryVec_mul_lazyWalkTransitionMatrix (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) (i j : V) :
    stationaryVec A i * lazyWalkTransitionMatrix A i j
      = stationaryVec A j * lazyWalkTransitionMatrix A j i := by
  have hDB : stationaryVec A i * walkTransitionMatrix A i j
      = stationaryVec A j * walkTransitionMatrix A j i :=
    walk_detailed_balance_measure A hA hd i j
  rcases Decidable.em (i = j) with h | h
  · subst h
    ring
  · rw [lazyWalkTransitionMatrix_apply, lazyWalkTransitionMatrix_apply,
      if_neg h, if_neg (fun hh => h hh.symm), add_zero, add_zero]
    linear_combination (2 : ℝ)⁻¹ * hDB

/-- The adjoint lazy operator fixes the stationary distribution: `π` is
stationary for the lazy walk. -/
theorem lazyWalkTransitionMatrixTranspose_mulVec_stationaryVec
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] :
    (lazyWalkTransitionMatrix A)ᵀ *ᵥ stationaryVec A
      = stationaryVec A := by
  have hplain : (walkTransitionMatrix A)ᵀ *ᵥ stationaryVec A
      = stationaryVec A := walk_isStationary A hA hd
  calc (lazyWalkTransitionMatrix A)ᵀ *ᵥ stationaryVec A
      = (2 : ℝ)⁻¹ • ((walkTransitionMatrix A)ᵀ *ᵥ stationaryVec A
          + (1 : Matrix V V ℝ) *ᵥ stationaryVec A) := by
            rw [lazyWalkTransitionMatrix, Matrix.transpose_smul,
              Matrix.transpose_add, Matrix.transpose_one,
              Matrix.smul_mulVec_assoc, Matrix.add_mulVec]
      _ = stationaryVec A := by
            rw [hplain, Matrix.one_mulVec]
            ext i
            have h2 : (2 : ℝ)⁻¹ * (stationaryVec A i + stationaryVec A i)
                = stationaryVec A i := by
              field_simp
            simpa [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using h2

/-- **Attainment persists**: once the lazy law has reached the
stationary distribution it stays there forever. The QA's every-time
exact-mixing pins run through this. -/
theorem lazyWalkDistribution_add_stationary (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (t s : ℕ) (x : V)
    (h : lazyWalkDistribution A t x = stationaryVec A) :
    lazyWalkDistribution A (t + s) x = stationaryVec A := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
    have hshift : t + (s + 1) = t + s + 1 := Nat.add_assoc t s 1
    rw [hshift]
    have hstep : lazyWalkDistribution A (t + s + 1) x
        = (lazyWalkTransitionMatrix A)ᵀ *ᵥ lazyWalkDistribution A (t + s) x :=
      lazyWalkDistribution_succ A (t + s) x
    rw [hstep, ih,
      lazyWalkTransitionMatrixTranspose_mulVec_stationaryVec A hA hd]

/-! ## The density and the χ² distance, lazy forms -/

/-- The π-density of the lazy walk law. Junk value `0` wherever
`π i = 0` (positive degrees rule that out). -/
noncomputable def lazyWalkDensity (A : WAdj (V := V)) (t : ℕ) (x : V) :
    V → ℝ :=
  fun i => lazyWalkDistribution A t x i / stationaryVec A i

/-- The lazy density agrees with the plain one at time zero — the two
walks share their initial condition, so the delivered connectivity mode
derivation (a statement about `walkDensity A 0 x − 1`) applies to the
lazy centered density verbatim. -/
theorem lazyWalkDensity_zero (A : WAdj (V := V)) (x : V) :
    lazyWalkDensity A 0 x = walkDensity A 0 x := by
  funext i
  simp only [lazyWalkDensity, walkDensity]
  rw [lazyWalkDistribution_zero, walkDistribution_zero]

/-- **The density evolution equation, lazy form**: `h_{t+1} =
P_L *ᵥ h_t` — detailed balance for the lazy operator in action. -/
theorem lazyWalkDensity_succ (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    lazyWalkDensity A (t + 1) x
      = lazyWalkTransitionMatrix A *ᵥ lazyWalkDensity A t x := by
  have hpos : ∀ i, stationaryVec A i ≠ 0 := fun i =>
    ne_of_gt (stationaryVec_pos A hd i)
  have hterm : ∀ (j i : V),
      lazyWalkTransitionMatrix A i j * lazyWalkDistribution A t x i
          / stationaryVec A j
      = lazyWalkTransitionMatrix A j i
          * (lazyWalkDistribution A t x i / stationaryVec A i) := by
    intro j i
    have hDB : stationaryVec A i * lazyWalkTransitionMatrix A i j
        = stationaryVec A j * lazyWalkTransitionMatrix A j i :=
      stationaryVec_mul_lazyWalkTransitionMatrix A hA hd i j
    have hπi := hpos i
    have hπj := hpos j
    rw [← mul_div_assoc, div_eq_div_iff hπj hπi]
    linear_combination lazyWalkDistribution A t x i * hDB
  funext j
  simp only [lazyWalkDensity]
  rw [lazyWalkDistribution_succ A t x]
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => hterm j i

/-- **Centered evolution, lazy form**: `h_t − 1 = P_Lᵗ *ᵥ (h₀ − 1)`. -/
theorem lazyWalkDensity_sub_one (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    lazyWalkDensity A t x - 1
      = (lazyWalkTransitionMatrix A ^ t) *ᵥ (lazyWalkDensity A 0 x - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hP1 : lazyWalkTransitionMatrix A *ᵥ (1 : V → ℝ) = 1 :=
      lazyWalkTransitionMatrix_mulVec_one A hd
    rw [lazyWalkDensity_succ A hA hd t x, pow_succ',
      ← Matrix.mulVec_mulVec]
    calc lazyWalkTransitionMatrix A *ᵥ lazyWalkDensity A t x - 1
        = lazyWalkTransitionMatrix A *ᵥ lazyWalkDensity A t x
            - lazyWalkTransitionMatrix A *ᵥ (1 : V → ℝ) := by rw [hP1]
      _ = lazyWalkTransitionMatrix A *ᵥ (lazyWalkDensity A t x - 1) :=
            (Matrix.mulVec_sub _ _ _).symm
      _ = lazyWalkTransitionMatrix A *ᵥ
          ((lazyWalkTransitionMatrix A ^ t) *ᵥ
              (lazyWalkDensity A 0 x - 1)) := by
            rw [ih]

/-- **The χ² mixing distance, lazy form** — stated in the sum-div
shape so the delivered `klDiv_le_sum_sq_div` composes by `.trans`
(the scoping lesson of the continuous twin's `_eq_sum_div`). -/
noncomputable def lazyChiSquareDistance (A : WAdj (V := V)) (t : ℕ)
    (x : V) : ℝ :=
  ∑ i, (lazyWalkDistribution A t x i - stationaryVec A i)^2
    / stationaryVec A i

/-- The χ² distance in density form — the π-weighted inner product of
the centered density with itself. -/
theorem lazyChiSquareDistance_eq_sum_smul (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) (x : V) :
    lazyChiSquareDistance A t x
      = ∑ i, stationaryVec A i * (lazyWalkDensity A t x i - 1)^2 := by
  have hpos : ∀ i, stationaryVec A i ≠ 0 := fun i =>
    ne_of_gt (stationaryVec_pos A hd i)
  simp only [lazyChiSquareDistance, lazyWalkDensity]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hπi := hpos i
  field_simp
  ring

/-- The `t = 0` value: the same point-mass normalization as the plain
walk, `(π x)⁻¹ − 1`. -/
theorem lazyChiSquareDistance_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (x : V) :
    lazyChiSquareDistance A 0 x = (stationaryVec A x)⁻¹ - 1 := by
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
    rw [Finset.sum_congr rfl fun i hi => hoff i hi, hrest]
  rw [lazyChiSquareDistance, lazyWalkDistribution_zero,
    hsplit fun i =>
      ((Pi.single x (1 : ℝ) : V → ℝ) i - stationaryVec A i)^2
        / stationaryVec A i]
  rw [hon, Finset.sum_congr rfl fun i hi => hoff i hi, hrest]
  have hfin : stationaryVec A x * (((1 - stationaryVec A x)^2
        / stationaryVec A x) + (1 - stationaryVec A x))
      = stationaryVec A x * ((stationaryVec A x)⁻¹ - 1) := by
    field_simp
    ring
  exact mul_left_cancel₀ hπx hfin

/-! ## The signless engine: `μ ≤ 2` -/

/-- Entrywise quadratic form of the degree matrix: `∑ i, deg i · u i²`. -/
theorem quadForm_degreeMatrix_eq (A : WAdj (V := V)) (u : V → ℝ) :
    quadForm (degreeMatrix A) u = ∑ i, deg A i * u i * u i := by
  have h0 : ∀ i j : V, j ≠ i →
      (degreeMatrix A) i j * u i * u j = 0 := by
    intro i j hj
    rw [degreeMatrix, dif_neg (fun hh => hj hh.symm)]
    simp
  rw [quadForm_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single
    (f := fun j => (degreeMatrix A) i j * u i * u j) i
    (fun j _ hj => h0 i j hj)
    (fun hi => absurd (Finset.mem_univ i) hi),
    degreeMatrix, dif_pos rfl]

omit [DecidableEq V] in
/-- The quadratic form of a matrix difference splits. -/
theorem quadForm_sub_eq (M N : Matrix V V ℝ) (y : V → ℝ) :
    quadForm (M - N) y = quadForm M y - quadForm N y := by
  rw [quadForm, Matrix.sub_mulVec, Matrix.dotProduct_sub, quadForm,
    quadForm]

omit [DecidableEq V] in
/-- The quadratic form of a matrix sum splits. -/
theorem quadForm_add_eq (M N : Matrix V V ℝ) (y : V → ℝ) :
    quadForm (M + N) y = quadForm M y + quadForm N y := by
  rw [quadForm, Matrix.add_mulVec, Matrix.dotProduct_add, quadForm,
    quadForm]

/-- **The signless sum-of-squares**: the quadratic form of the signless
Laplacian `D + A` is half the edge sum of squared *sums* —
`uᵀ(D + A)u = (1/2) ∑ i, ∑ j, A i j (u i + u j)²` at any symmetric `A`.
This is the positivity certificate that bounds the normalized spectrum
above by `2`. -/
theorem quadForm_degreeMatrix_add_eq_half_sum (A : WAdj (V := V))
    (hA : A.IsSymm) (u : V → ℝ) :
    quadForm (degreeMatrix A + A) u
      = (1/2) * ∑ i, ∑ j, A i j * (u i + u j)^2 := by
  have hsym : ∀ i j : V, A j i = A i j := by
    intro i j
    rw [← Matrix.transpose_apply A i j, hA.eq]
  have hdeg2 : ∑ i, ∑ j, A i j * (u j * u j)
      = ∑ j, deg A j * u j * u j := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset V))
      (t := (Finset.univ : Finset V))
      (f := fun i j => A i j * (u j * u j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl fun i _ => mul_comm (A i j) (u j * u j),
      ← Finset.mul_sum]
    have hcol : ∑ i, A i j = deg A j := by
      have hrw : deg A j = ∑ i, A j i := rfl
      rw [hrw]
      exact Finset.sum_congr rfl fun i _ => (hsym i j).symm
    rw [hcol]
    ring
  have hsplit : quadForm (degreeMatrix A + A) u
      = ∑ i, deg A i * u i * u i + ∑ i, ∑ j, A i j * u i * u j := by
    rw [quadForm_add_eq, quadForm_degreeMatrix_eq, quadForm_eq_sum]
  have hexp : ∀ i j : V, A i j * (u i + u j)^2
      = A i j * (u i * u i) + A i j * (u j * u j)
        + 2 * (A i j * u i * u j) := by
    intro i j
    ring
  have hdeg : ∑ i, ∑ j, A i j * (u i * u i)
      = ∑ i, deg A i * u i * u i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun j _ => mul_comm (A i j) (u i * u i),
      ← Finset.mul_sum]
    have hd : deg A i = ∑ j, A i j := rfl
    rw [hd]
    ring
  have hrhs : (1/2) * ∑ i, ∑ j, A i j * (u i + u j)^2
      = ∑ i, deg A i * u i * u i + ∑ i, ∑ j, A i j * u i * u j := by
    have h1 : ∑ i, ∑ j, A i j * (u i + u j)^2
        = ∑ i, ∑ j, (A i j * (u i * u i) + A i j * (u j * u j)
            + 2 * (A i j * u i * u j)) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hexp i j
    have h2 : ∑ i, ∑ j, (A i j * (u i * u i) + A i j * (u j * u j)
            + 2 * (A i j * u i * u j))
        = (∑ i, ∑ j, A i j * (u i * u i)
              + ∑ i, ∑ j, A i j * (u j * u j))
          + 2 * ∑ i, ∑ j, (A i j * u i * u j) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    rw [h1, h2, hdeg, hdeg2]
    ring
  rw [hsplit, hrhs]

/-- **The two-sided spectral bound's conjugation identity**:
`xᵀ(2·1 − L_sym)x = uᵀ(D + A)u` at `u = (1/√D) *ᵥ x` — the quadratic
form of `2·1 − L_sym` is the signless form of the unstretched vector,
through the proved congruence `√D L_sym √D = L` and `D − L = A`. -/
theorem quadForm_two_sub_normalizedLaplacian_eq (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) (x : V → ℝ) :
    quadForm ((2 : ℝ) • 1 - normalizedLaplacian A) x
      = quadForm (degreeMatrix A + A) (degreeInvSqrt A *ᵥ x) := by
  have hstretch : degreeSqrt A *ᵥ (degreeInvSqrt A *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, degreeSqrt_mul_degreeInvSqrt A hd,
      Matrix.one_mulVec]
  have hdx : Matrix.dotProduct x x
      = ∑ i, deg A i * (degreeInvSqrt A *ᵥ x) i
          * (degreeInvSqrt A *ᵥ x) i := by
    have h := dotProduct_degreeSqrt_mulVec A
      (fun i => le_of_lt (hd i)) (degreeInvSqrt A *ᵥ x)
    rw [hstretch] at h
    exact h
  have hqs : quadForm (normalizedLaplacian A) x
      = quadForm (laplacian A) (degreeInvSqrt A *ᵥ x) := by
    have h := quadForm_laplacian_eq_quadForm_normalizedLaplacian A hd
      (degreeInvSqrt A *ᵥ x)
    rw [hstretch] at h
    exact h.symm
  have hq2 : quadForm ((2 : ℝ) • 1 - normalizedLaplacian A) x
      = 2 * Matrix.dotProduct x x - quadForm (normalizedLaplacian A) x := by
    rw [quadForm_sub_eq, quadForm, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, Matrix.dotProduct_smul, smul_eq_mul]
  have hL : quadForm (laplacian A) (degreeInvSqrt A *ᵥ x)
      = (∑ i, deg A i * (degreeInvSqrt A *ᵥ x) i
            * (degreeInvSqrt A *ᵥ x) i)
        - ∑ i, ∑ j, A i j * (degreeInvSqrt A *ᵥ x) i
            * (degreeInvSqrt A *ᵥ x) j := by
    have hlap : laplacian A = degreeMatrix A - A := rfl
    rw [hlap, quadForm_sub_eq, quadForm_degreeMatrix_eq, quadForm_eq_sum]
  have hR : quadForm (degreeMatrix A + A) (degreeInvSqrt A *ᵥ x)
      = (∑ i, deg A i * (degreeInvSqrt A *ᵥ x) i
            * (degreeInvSqrt A *ᵥ x) i)
        + ∑ i, ∑ j, A i j * (degreeInvSqrt A *ᵥ x) i
            * (degreeInvSqrt A *ᵥ x) j := by
    rw [quadForm_add_eq, quadForm_degreeMatrix_eq, quadForm_eq_sum]
  rw [hq2, hqs, hL, hdx]
  linarith

/-- **The signless positivity certificate**: at nonnegative weights,
`xᵀ(2·1 − L_sym)x ≥ 0` — every normalized-Laplacian eigenvalue is at
most `2`. The `hnn` hypothesis is load-bearing (fenced in QA at a
negative-diagonal fixture with positive degrees). -/
theorem quadForm_two_sub_normalizedLaplacian_nonneg
    (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) (x : V → ℝ) :
    0 ≤ quadForm ((2 : ℝ) • 1 - normalizedLaplacian A) x := by
  rw [quadForm_two_sub_normalizedLaplacian_eq A hd x,
    quadForm_degreeMatrix_add_eq_half_sum A hA (degreeInvSqrt A *ᵥ x)]
  refine mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => ?_)
  exact mul_nonneg (hnn i j) (sq_nonneg _)

/-- Every normalized-Laplacian eigenvalue is nonnegative (PSD at the
unit eigenvector). -/
theorem eigvalOf_normalizedLaplacian_nonneg (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (i : V) :
    0 ≤ eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i := by
  rw [← quadForm_eigvecOf_self (normalizedLaplacian_symmetric A hA) i]
  exact normalizedLaplacian_psd A hA hnn hd _

/-- **Every normalized-Laplacian eigenvalue is at most `2`** — the
signless certificate at the unit eigenvector. On bipartite graphs the
bound is attained (the top mode `|1 − μ| = 1` is exactly the boundary
the plain walk's certificates die on; QA pins the saturation on `K₂`). -/
theorem eigvalOf_normalizedLaplacian_le_two (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (i : V) :
    eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≤ 2 := by
  have hn := quadForm_two_sub_normalizedLaplacian_nonneg A hnn hA hd
    (eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i)
  have hq : quadForm ((2 : ℝ) • 1 - normalizedLaplacian A)
      (eigvecOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i)
      = 2 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i := by
    have hev : normalizedLaplacian A *ᵥ
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
      = eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i •
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i) :=
      (isHermitian_of_isSymm
        (normalizedLaplacian_symmetric A hA)).mulVec_eigenvectorBasis i
    have hun : Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i) = 1 := by
      simpa [Matrix.dotProduct] using
        eigvecOf_inner (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i i
    rw [quadForm, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, hev, Matrix.dotProduct_sub,
      Matrix.dotProduct_smul, Matrix.dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hun, mul_one, mul_one]
  rw [hq] at hn
  linarith

/-- **The spectral-gap cap**: `λ₂(L_sym) ≤ 2` — sortedness gives
`evals ⟨1⟩ ≤ evals ⟨last⟩`, the last entry is some `eigvalOf i`
(`evals_mem_eigvalOf`), and the pointwise signless bound above closes.
Together with `eigvalOf_normalizedLaplacian_le_two` this says the whole
normalized spectrum lives in `[0, 2]`; the cap is what makes the lazy
rate `1 − λ₂/2` nonnegative without a strictness hypothesis (it is
exactly `0` on `K₂`, where the lazy walk mixes in one step). -/
theorem secondEval_normalizedLaplacian_le_two (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (hcard : 2 ≤ Fintype.card V) :
    secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard ≤ 2 := by
  have h1 : (1 : ℕ) < Fintype.card V := lt_of_lt_of_le (by omega) hcard
  have h2 : Fintype.card V - 1 < Fintype.card V := by omega
  have hlast : evals (normalizedLaplacian_symmetric A hA) ⟨1, h1⟩
      ≤ evals (normalizedLaplacian_symmetric A hA)
        ⟨Fintype.card V - 1, h2⟩ :=
    evals_sorted _ (Fin.mk_le_mk.mpr (by omega))
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (normalizedLaplacian_symmetric A hA)
    ⟨Fintype.card V - 1, h2⟩
  calc secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard
      = evals (normalizedLaplacian_symmetric A hA) ⟨1, h1⟩ := rfl
    _ ≤ evals (normalizedLaplacian_symmetric A hA)
        ⟨Fintype.card V - 1, h2⟩ := hlast
    _ = eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i := hi
    _ ≤ 2 := eigvalOf_normalizedLaplacian_le_two A hA hnn hd i

/-! ## The spectral certificate: intrinsic rate on non-bipartite input -/

/-- **Walk flip-propagation**: a function that flips sign along every
edge of a simple graph flips sign along every walk — `u b =
(−1)^{|p|} · u a`. The engine's parity mechanism, stated at the pure
graph level; also the mechanism behind every-closed-walk-even
witnesses at bipartite fixtures (the QA's isolation companions). -/
theorem walk_eq_neg_one_pow_length_mul_of_forall_adj {V : Type}
    [DecidableEq V] {G : SimpleGraph V} (u : V → ℝ)
    (hflip : ∀ i j : V, G.Adj i j → u j = -u i)
    {a b : V} (p : G.Walk a b) :
    u b = (-1) ^ p.length * u a := by
  induction p with
  | nil => simp
  | @cons x k y hadj rest ih =>
    rw [SimpleGraph.Walk.length_cons, ih, hflip x k hadj,
      show (-1 : ℝ) ^ (rest.length + 1) = -((-1) ^ rest.length) from by
        rw [pow_succ]; ring]
    ring

/-- **The strict signless bound**: on a connected support graph
carrying an odd closed walk, every normalized-Laplacian eigenvalue is
strictly below `2` — the classical "bipartite ⟺ `λ_max = 2`"
dichotomy's strict half, at the shelf's honest non-bipartite interface
(`Odd p.length`, statement-identical to the primitivity supplier's).
An eigenvalue `μ = 2` makes `uᵀ(D + A)u = 0` at the unstretched
conjugate `u = D^{-1/2} *ᵥ v` (the delivered congruence), the
signless SOS then forces `u` to flip along every support edge, the odd
walk forces `u = 0` at its base, and connectivity propagates `u = 0`
everywhere — contradicting the unit eigenvector. -/
theorem eigvalOf_normalizedLaplacian_lt_two_of_odd_walk
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i)
    (hconn : (supportGraph A hA).Connected)
    {w : V} (p : (supportGraph A hA).Walk w w) (hp : Odd p.length)
    (i : V) :
    eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i < 2 := by
  have hL : (normalizedLaplacian A).IsSymm :=
    normalizedLaplacian_symmetric A hA
  by_contra hcon
  push_neg at hcon
  have hμ2 : eigvalOf (normalizedLaplacian A) hL i = 2 :=
    le_antisymm (eigvalOf_normalizedLaplacian_le_two A hA hnn hd i) hcon
  set v : V → ℝ :=
    eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) i
    with hv
  set u : V → ℝ := degreeInvSqrt A *ᵥ v with hu
  have hvv : v = eigvecOf (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) i := hv
  have hun : Matrix.dotProduct v v = 1 := by
    rw [hvv]
    simpa [Matrix.dotProduct] using
      eigvecOf_inner (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i i
  have hqf : quadForm ((2 : ℝ) • 1 - normalizedLaplacian A) v
      = 2 - eigvalOf (normalizedLaplacian A) hL i := by
    have hev : normalizedLaplacian A *ᵥ v
        = eigvalOf (normalizedLaplacian A) hL i • v :=
      (isHermitian_of_isSymm hL).mulVec_eigenvectorBasis i
    rw [quadForm, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
      Matrix.one_mulVec, hev, Matrix.dotProduct_sub,
      Matrix.dotProduct_smul, Matrix.dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hun, mul_one, mul_one]
  have hu0 : quadForm (degreeMatrix A + A) u = 0 := by
    rw [hu, ← quadForm_two_sub_normalizedLaplacian_eq A hd v, hqf, hμ2]
    norm_num
  have hsum : ∑ j, ∑ k, A j k * (u j + u k) ^ 2 = 0 := by
    have h := quadForm_degreeMatrix_add_eq_half_sum A hA u
    rw [hu0] at h
    linarith
  have hterms : ∀ j k : V, A j k * (u j + u k) ^ 2 = 0 := by
    intro j k
    have hinner : ∀ j' ∈ (Finset.univ : Finset V),
        0 ≤ ∑ k', A j' k' * (u j' + u k') ^ 2 :=
      fun j' _ => Finset.sum_nonneg fun k' _ =>
        mul_nonneg (hnn j' k') (sq_nonneg _)
    have h := (Finset.sum_eq_zero_iff_of_nonneg hinner).1 hsum
    have hj := h j (Finset.mem_univ j)
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (hnn j k) (sq_nonneg _))).1 hj k
      (Finset.mem_univ k)
  have hflip : ∀ j k : V, (supportGraph A hA).Adj j k → u k = -u j := by
    intro j k hadj
    have hpos : 0 < A j k := (supportGraph_adj.1 hadj).2
    have hz := hterms j k
    have hsq : (u j + u k) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (ne_of_gt hpos)
      · exact h
    have h0 : u j + u k = 0 := sq_eq_zero_iff.mp hsq
    linarith
  have hpar := walk_eq_neg_one_pow_length_mul_of_forall_adj u hflip p
  rw [hp.neg_one_pow] at hpar
  have hw0 : u w = 0 := by linarith
  have hzero : ∀ z : V, u z = 0 := by
    intro z
    obtain ⟨q⟩ := hconn.1 z w
    have hq := walk_eq_neg_one_pow_length_mul_of_forall_adj u hflip q
    rw [hw0] at hq
    rcases mul_eq_zero.mp hq.symm with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · exact h
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0] at hun
    norm_num at hun
  have hst : degreeSqrt A *ᵥ u = v := by
    rw [hu, Matrix.mulVec_mulVec, degreeSqrt_mul_degreeInvSqrt A hd,
      Matrix.one_mulVec]
  rw [show u = 0 from funext hzero, Matrix.mulVec_zero] at hst
  exact hvne hst.symm

/-- **The strict signless bound, sorted-spectrum form**: every sorted
entry of the normalized-Laplacian spectrum is strictly below `2` on
the odd-walk class (each sorted entry is some basis eigenvalue). -/
theorem evals_normalizedLaplacian_lt_two_of_odd_walk
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i)
    (hconn : (supportGraph A hA).Connected)
    {w : V} (p : (supportGraph A hA).Walk w w) (hp : Odd p.length)
    (k : Fin (Fintype.card V)) :
    evals (normalizedLaplacian_symmetric A hA) k < 2 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (normalizedLaplacian_symmetric A hA) k
  rw [hi]
  exact eigvalOf_normalizedLaplacian_lt_two_of_odd_walk A hA hnn hd hconn
    p hp i

/-- **The certificate rate dominates every decaying walk factor**:
`|1 − μ| ≤ max (1 − λ₂) (λ_max − 1)` for every nonzero mode — PSD and
the below-gap plumbing supply `λ₂ ≤ μ`, the sorted-extremes bridge
supplies `μ ≤ λ_max`. Stated unconditionally in the graph (on
bipartite input the max merely reaches `1`); the odd-walk class is
where the certificate theorem below makes it strictly contractive. -/
theorem abs_one_sub_eigvalOf_le_max
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V)
    {i : V} (hne : eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0) :
    |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i|
      ≤ max (1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard)
          (evals (normalizedLaplacian_symmetric A hA)
            ⟨Fintype.card V - 1, by omega⟩ - 1) := by
  have hμ0 := eigvalOf_normalizedLaplacian_nonneg A hA hnn hd i
  have hμlow := secondEval_le_eigvalOf_normalizedLaplacian_of_ne_zero
    A hA hnn hd hcard hne
  have hμhigh : eigvalOf (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) i
      ≤ evals (normalizedLaplacian_symmetric A hA)
        ⟨Fintype.card V - 1, by omega⟩ :=
    eigvalOf_le_evals_last _ (by omega) i
  rw [abs_le]
  constructor
  · linarith [hμhigh, le_max_right (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard)
      (evals (normalizedLaplacian_symmetric A hA)
        ⟨Fintype.card V - 1, by omega⟩ - 1)]
  · linarith [hμlow, le_max_left (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard)
      (evals (normalizedLaplacian_symmetric A hA)
        ⟨Fintype.card V - 1, by omega⟩ - 1)]

/-- **The plain family's `r < 1` certificate exists on the odd-walk
class**: the intrinsic-rate family's non-bipartite member. The rate is
computed, not caller-supplied — `max (1 − λ₂) (λ_max − 1)` with
`0 < λ₂` (connectivity) and `λ_max < 2` (the strict signless engine),
so the max is strictly below one. -/
theorem exists_lt_one_rate_of_odd_walk
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected)
    {w : V} (p : (supportGraph A hA).Walk w w) (hp : Odd p.length) :
    ∃ r : ℝ, r < 1 ∧ ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r :=
  ⟨max (1 - secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard)
      (evals (normalizedLaplacian_symmetric A hA)
        ⟨Fintype.card V - 1, by omega⟩ - 1),
    max_lt (by
      linarith [secondEval_normalizedLaplacian_pos_of_connected A hA hnn
        hd hcard hconn])
      (by
        linarith [evals_normalizedLaplacian_lt_two_of_odd_walk A hA hnn hd
          hconn p hp ⟨Fintype.card V - 1, by omega⟩]),
    fun i hi =>
      abs_one_sub_eigvalOf_le_max A hA hnn hd hcard hi⟩

/-- **The display-friendly positive certificate**: an `r ∈ (0, 1)`
dominating every decaying factor — the computed rate inflated to the
open interval, needed because `r = 0` is an honest corner (a looped
triangle mixes exactly in one step) and depth-form log thresholds
divide by `log (1/r)`. -/
theorem exists_pos_lt_one_rate_of_odd_walk
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected)
    {w : V} (p : (supportGraph A hA).Walk w w) (hp : Odd p.length) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r := by
  obtain ⟨r, hr1, hrate⟩ :=
    exists_lt_one_rate_of_odd_walk A hA hnn hd hcard hconn p hp
  have h1 : r ≤ max r 0 := le_max_left r 0
  have h2 : 0 ≤ max r 0 := le_max_right r 0
  have h3 : max r 0 < 1 := max_lt_iff.2 ⟨hr1, by norm_num⟩
  refine ⟨(max r 0 + 1) / 2, by linarith, by linarith, ?_⟩
  intro i hi
  exact (hrate i hi).trans (by linarith)

/-- **The plain χ² mixing bound at the computed spectral rate** — the
plain family's display twin (the lazy family's
`lazyChiSquareDistance_le_of_connected` computes `1 − λ₂/2` under
connectivity alone; the plain walk's factors are two-sided in the
spectrum, so the computed rate is `max (1 − λ₂) (λ_max − 1)`):
`χ²(t, x) ≤ max(1 − λ₂, λ_max − 1)^{2t} · ((π x)⁻¹ − 1)` on every
connected symmetric-nonnegative positive-degree network with
`2 ≤ card V`. The statement is unconditional in the parity of the
graph — on the odd-walk (non-bipartite) class
`exists_lt_one_rate_of_odd_walk` makes the displayed rate strictly
contractive, which is the certificate's whole content; on bipartite
input the display saturates at `1` and the bound is the trivial
`t = 0` normalization. -/
theorem chiSquareDistance_le_max_rate
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) (t : ℕ) (x : V) :
    chiSquareDistance A t x
      ≤ (max (1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard)
            (evals (normalizedLaplacian_symmetric A hA)
              ⟨Fintype.card V - 1, by omega⟩ - 1)) ^ (2 * t)
          * ((stationaryVec A x)⁻¹ - 1) :=
  chiSquareDistance_le_of_connected A hA hnn hd hconn _ t x
    (fun _ hi =>
      abs_one_sub_eigvalOf_le_max A hA hnn hd hcard hi)

/-- **The TV shadow at the computed spectral rate** — the plain twin of
`lazyWalkDistribution_tvDistance_le_of_connected`. -/
theorem walkDistribution_tvDistance_le_max_rate
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) (t : ℕ) (x : V) :
    tvDistance (walkDistribution A t x) (stationaryVec A)
      ≤ (1/2) * Real.sqrt
          ((max (1 - secondEval (normalizedLaplacian A)
                  (normalizedLaplacian_symmetric A hA) hcard)
              (evals (normalizedLaplacian_symmetric A hA)
                ⟨Fintype.card V - 1, by omega⟩ - 1)) ^ (2 * t)
            * ((stationaryVec A x)⁻¹ - 1)) := by
  refine (walkDistribution_tvDistance_le A hd t x).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt
      (chiSquareDistance_le_max_rate A hA hnn hd hcard hconn t x))
    (by norm_num)

/-! ## The lazy decay engine -/

/-- **The lazy commutation**: `√D · P_L = (1 − (1/2)·L_sym) · √D` — the
average of the plain commutation `√D P = (1 − L_sym) √D` with the
trivial `√D · 1 = √D`. -/
theorem degreeSqrt_mul_lazyWalkTransitionMatrix_eq (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    degreeSqrt A * lazyWalkTransitionMatrix A
      = (1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) * degreeSqrt A := by
  have hP := degreeSqrt_mul_walkTransitionMatrix_eq A hd
  have htwo : ∀ M : Matrix V V ℝ,
      ((1 : Matrix V V ℝ) - M) + 1 = (2 : ℝ) • 1 - M := by
    intro M
    ext i j
    rcases Decidable.em (i = j) with h | h
    · simp [h]
      ring
    · simp [h]
  calc degreeSqrt A * lazyWalkTransitionMatrix A
      = (2 : ℝ)⁻¹ • (degreeSqrt A * walkTransitionMatrix A
          + degreeSqrt A) := by
            rw [lazyWalkTransitionMatrix, Matrix.mul_smul,
              Matrix.mul_add, Matrix.mul_one]
      _ = (2 : ℝ)⁻¹ • ((1 - normalizedLaplacian A) * degreeSqrt A
          + degreeSqrt A) := by
            rw [hP]
      _ = (2 : ℝ)⁻¹ • ((1 - normalizedLaplacian A) * degreeSqrt A
          + (1 : Matrix V V ℝ) * degreeSqrt A) := by
            rw [Matrix.one_mul]
      _ = (2 : ℝ)⁻¹ • (((1 : Matrix V V ℝ) - normalizedLaplacian A)
            * degreeSqrt A
          + (1 : Matrix V V ℝ) * degreeSqrt A) := by
            rfl
      _ = (2 : ℝ)⁻¹ • ((((1 : Matrix V V ℝ) - normalizedLaplacian A)
            + 1) * degreeSqrt A) := by
            rw [← Matrix.add_mul]
      _ = (2 : ℝ)⁻¹ • (((2 : ℝ) • 1 - normalizedLaplacian A)
          * degreeSqrt A) := by
            rw [htwo _]
      _ = ((1 : Matrix V V ℝ)
            - (2 : ℝ)⁻¹ • normalizedLaplacian A) * degreeSqrt A := by
            rw [← Matrix.smul_mul, smul_sub, smul_smul,
              inv_mul_cancel₀ two_ne_zero, one_smul]

/-- **The conjugated-power transfer, lazy form**: `√D *ᵥ (P_Lᵗ *ᵥ g)`
is the `t`-th power of the symmetric lazy operator
`1 − (1/2)·L_sym` acting on `√D *ᵥ g`. -/
theorem degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix
    (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i) (t : ℕ) (g : V → ℝ) :
    degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g)
      = ((1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) ^ t)
          *ᵥ (degreeSqrt A *ᵥ g) := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ (t + 1)) *ᵥ g)
        = degreeSqrt A *ᵥ (lazyWalkTransitionMatrix A *ᵥ
            ((lazyWalkTransitionMatrix A ^ t) *ᵥ g)) := by
              rw [pow_succ', Matrix.mulVec_mulVec g
                (lazyWalkTransitionMatrix A)
                (lazyWalkTransitionMatrix A ^ t)]
      _ = (degreeSqrt A * lazyWalkTransitionMatrix A) *ᵥ
            ((lazyWalkTransitionMatrix A ^ t) *ᵥ g) :=
              Matrix.mulVec_mulVec _ _ _
      _ = ((1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) * degreeSqrt A) *ᵥ
            ((lazyWalkTransitionMatrix A ^ t) *ᵥ g) := by
              rw [degreeSqrt_mul_lazyWalkTransitionMatrix_eq A hd]
      _ = (1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) *ᵥ
            (degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g)) :=
              (Matrix.mulVec_mulVec _ _ _).symm
      _ = (1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) *ᵥ
            (((1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) ^ t) *ᵥ
              (degreeSqrt A *ᵥ g)) := by rw [ih]
      _ = ((1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) ^ (t + 1)) *ᵥ
            (degreeSqrt A *ᵥ g) := by
              rw [pow_succ', ← Matrix.mulVec_mulVec (degreeSqrt A *ᵥ g)
                (1 - (2 : ℝ)⁻¹ • normalizedLaplacian A)
                ((1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) ^ t)]

/-- **The eigenaction of the symmetric lazy operator** on the
normalized-Laplacian eigenbasis: the mode factor is `1 − μ/2` — the
number the whole lazy program runs on. -/
theorem eigvecOf_dotProduct_one_sub_half_normalizedLaplacian_mulVec
    (A : WAdj (V := V)) (hA : A.IsSymm) (i : V) (x : V → ℝ) :
    Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        ((1 - (2 : ℝ)⁻¹ • normalizedLaplacian A) *ᵥ x)
      = (1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i / 2)
          * Matrix.dotProduct
              (eigvecOf (normalizedLaplacian A)
                (normalizedLaplacian_symmetric A hA) i) x := by
  have hev : normalizedLaplacian A *ᵥ
      (eigvecOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i)
    = eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i •
      (eigvecOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i) :=
    (isHermitian_of_isSymm
      (normalizedLaplacian_symmetric A hA)).mulVec_eigenvectorBasis i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.dotProduct_sub,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_smul, (normalizedLaplacian_symmetric A hA).eq,
    Matrix.smul_mulVec_assoc, hev, smul_smul,
    Matrix.smul_dotProduct, smul_eq_mul, sub_mul, one_mul]
  ring

/-- **Eigencoordinate evolution, lazy form**: the `i`-th eigencoefficient
of the conjugated `t`-step lazy evolution is the initial coefficient
multiplied by `(1 − μ i/2)^t`. -/
theorem eigvecOf_dotProduct_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (t : ℕ) (g : V → ℝ) (i : V) :
    Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        (degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g))
      = (1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i / 2) ^ t
          * Matrix.dotProduct
              (eigvecOf (normalizedLaplacian A)
                (normalizedLaplacian_symmetric A hA) i)
              (degreeSqrt A *ᵥ g) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix A hd (t + 1) g,
      pow_succ', ← Matrix.mulVec_mulVec,
      eigvecOf_dotProduct_one_sub_half_normalizedLaplacian_mulVec A hA i,
      ← degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix A hd t g, ih,
      pow_succ', mul_assoc]

/-- **The Parseval-exact decay identity, lazy form**: the squared
Euclidean norm of the conjugated `t`-step lazy evolution is the
eigenvalue-weighted sum of squared initial eigencoordinates, each
weight `(1 − μ i/2)^t`. No inequality is lost here. -/
theorem dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (t : ℕ) (g : V → ℝ) :
    Matrix.dotProduct
        (degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g))
        (degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g))
      = ∑ i, ((1 - eigvalOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i / 2) ^ t
          * Matrix.dotProduct
              (eigvecOf (normalizedLaplacian A)
                (normalizedLaplacian_symmetric A hA) i)
              (degreeSqrt A *ᵥ g)) ^ 2 := by
  rw [dotProduct_eigvecOf (normalizedLaplacian_symmetric A hA) _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eigvecOf_dotProduct_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix
      A hA hd t g i, pow_two]

/-- **The ℓ² contraction in conjugated-norm form, lazy form** — the
clone of `dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix_le`
at the lazy factors: under the mode hypothesis (no component on the
zero-eigenvalue modes of `L_sym`) and the rate hypothesis (`r`
dominating every lazy factor `|1 − μ/2|`), the `t`-step lazy evolution
contracts the conjugated norm at rate `r ^ (2t)`. No sign hypothesis on
`r` — inherited from the plain engine's recorded design decision. -/
theorem dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix_contraction
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
            (normalizedLaplacian_symmetric A hA) i / 2| ≤ r) :
    Matrix.dotProduct
        (degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g))
        (degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g))
      ≤ r ^ (2 * t)
        * Matrix.dotProduct (degreeSqrt A *ᵥ g) (degreeSqrt A *ᵥ g) := by
  classical
  rw [dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix
    A hA hd t g]
  have hterm : ∀ i : V,
      ((1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i / 2) ^ t
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
            (normalizedLaplacian_symmetric A hA) i / 2) ^ t|
          = |1 - eigvalOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i / 2| ^ t :=
        abs_pow _ _
      have hle : |(1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i / 2) ^ t| ≤ r ^ t := by
        rw [habspow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hrate i hμ) t
      have key : ((1 - eigvalOf (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) i / 2) ^ t) ^ 2
          ≤ (r ^ t) ^ 2 := by
        rw [← sq_abs ((1 - eigvalOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i / 2) ^ t)]
        refine sq_le_sq' ?_ hle
        linarith [abs_nonneg ((1 - eigvalOf (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) i / 2) ^ t), hrt]
      have hrw : r ^ (2 * t) = (r ^ t) ^ 2 := by
        rw [mul_comm 2 t, pow_mul]
      rw [hrw, mul_pow]
      exact mul_le_mul_of_nonneg_right key (sq_nonneg _)
  calc ∑ i, ((1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i / 2) ^ t
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

/-- **The ℓ²(π) contraction, lazy form** — under the same mode/rate
shape as the plain engine, at the lazy factors. No sign hypothesis on
`r` (the plain engine's recorded design decision, inherited). -/
theorem sum_stationaryVec_smul_sq_pow_lazyWalkTransitionMatrix_le
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
            (normalizedLaplacian_symmetric A hA) i / 2| ≤ r) :
    ∑ i, stationaryVec A i
        * (((lazyWalkTransitionMatrix A ^ t) *ᵥ g) i) ^ 2
      ≤ r ^ (2 * t) * ∑ i, stationaryVec A i * (g i) ^ 2 := by
  have hvol : 0 ≤ vol A (Finset.univ : Finset V) :=
    Finset.sum_nonneg fun i _ => le_of_lt (hd i)
  have heng := dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix_contraction
    A hA hd g r t hmode hrate
  have hL := sum_stationaryVec_smul_sq_eq A hd
    fun i => ((lazyWalkTransitionMatrix A ^ t) *ᵥ g) i
  have hR := sum_stationaryVec_smul_sq_eq A hd g
  rw [hL, hR]
  calc (vol A (Finset.univ : Finset V))⁻¹
        * Matrix.dotProduct
            (degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g))
            (degreeSqrt A *ᵥ ((lazyWalkTransitionMatrix A ^ t) *ᵥ g))
      ≤ (vol A (Finset.univ : Finset V))⁻¹
          * (r ^ (2 * t)
            * Matrix.dotProduct (degreeSqrt A *ᵥ g)
              (degreeSqrt A *ᵥ g)) :=
        mul_le_mul_of_nonneg_left heng (inv_nonneg.mpr hvol)
    _ = r ^ (2 * t) * ((vol A (Finset.univ : Finset V))⁻¹
        * Matrix.dotProduct (degreeSqrt A *ᵥ g)
          (degreeSqrt A *ᵥ g)) := by ring

/-- **The intrinsic rate**: every nonzero mode's lazy factor is bounded
by `1 − λ₂(L_sym)/2` — PSD gives `0 ≤ μ`, the signless certificate
gives `μ ≤ 2`, and the delivered below-gap plumbing gives `λ₂ ≤ μ`. No
sign hypothesis on the rate is needed anywhere. -/
theorem abs_one_sub_half_eigvalOf_le_one_sub_half_secondEval
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V) {i : V}
    (hne : eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0) :
    |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i / 2|
      ≤ 1 - secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard / 2 := by
  have h0 := eigvalOf_normalizedLaplacian_nonneg A hA hnn hd i
  have h2 := eigvalOf_normalizedLaplacian_le_two A hA hnn hd i
  have hgap := secondEval_le_eigvalOf_normalizedLaplacian_of_ne_zero
    A hA hnn hd hcard hne
  have hdiv : secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2
      ≤ eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i / 2 := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact (div_le_div_iff₀ h2 h2).2 (mul_le_mul_of_nonneg_right hgap h2.le)
  have hpos : (0 : ℝ) ≤ 1 - eigvalOf (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) i / 2 := by linarith
  rw [abs_of_nonneg hpos]
  exact sub_le_sub (le_refl 1) hdiv

/-! ## The headline: the lazy χ² mixing bound at the intrinsic rate -/

/-- **The lazy χ² mixing bound** — the discrete mixing program's
periodicity fix: on every connected symmetric-nonnegative
positive-degree network with `2 ≤ card V`,
`χ²_lazy(t, x) ≤ (1 − λ₂(L_sym)/2)^{2t} · ((π x)⁻¹ − 1)`.
Connectivity is the only graph hypothesis — the rate is *intrinsic*
(the continuous family's recorded advantage, delivered on the discrete
side): on bipartite graphs, where the plain family's rate hypothesis is
provably unsatisfiable (`λ_max = 2` mode), the lazy rate `1 − λ₂/2`
still contracts. Pure hard crust. -/
theorem lazyChiSquareDistance_le_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) (t : ℕ) (x : V) :
    lazyChiSquareDistance A t x
      ≤ (1 - secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
          * ((stationaryVec A x)⁻¹ - 1) := by
  have hmode : ∀ i : V, eigvalOf (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) i = 0 →
      Matrix.dotProduct
        (eigvecOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i)
        (degreeSqrt A *ᵥ (lazyWalkDensity A 0 x - 1)) = 0 := by
    intro i hμ
    have hjoin : lazyWalkDensity A 0 x - 1
        = walkDensity A 0 x - 1 := by
      rw [lazyWalkDensity_zero]
    rw [hjoin]
    exact eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero
      A hA hnn hd hconn x hμ
  have hctr := sum_stationaryVec_smul_sq_pow_lazyWalkTransitionMatrix_le
    A hA hd (lazyWalkDensity A 0 x - 1)
    (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2) t hmode
    (fun i hi =>
      abs_one_sub_half_eigvalOf_le_one_sub_half_secondEval
        A hA hnn hd hcard hi)
  have hcenter : ∀ i : V, (lazyWalkDensity A t x i - 1)
      = ((lazyWalkTransitionMatrix A ^ t) *ᵥ
          (lazyWalkDensity A 0 x - 1)) i := by
    intro i
    rw [← congrFun (lazyWalkDensity_sub_one A hA hd t x) i,
      Pi.sub_apply, Pi.one_apply]
  rw [lazyChiSquareDistance_eq_sum_smul A hd t x]
  have hsum : ∑ i, stationaryVec A i * (lazyWalkDensity A t x i - 1)^2
      = ∑ i, stationaryVec A i
          * (((lazyWalkTransitionMatrix A ^ t) *ᵥ
              (lazyWalkDensity A 0 x - 1)) i)^2 :=
    Finset.sum_congr rfl fun i _ => by rw [hcenter i]
  rw [hsum]
  have h0 : ∑ i, stationaryVec A i * ((lazyWalkDensity A 0 x - 1) i)^2
      = lazyChiSquareDistance A 0 x := by
    rw [lazyChiSquareDistance_eq_sum_smul A hd 0 x]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Pi.sub_apply, Pi.one_apply]
  calc ∑ i, stationaryVec A i
        * (((lazyWalkTransitionMatrix A ^ t) *ᵥ
            (lazyWalkDensity A 0 x - 1)) i)^2
      ≤ (1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
          * ∑ i, stationaryVec A i
              * ((lazyWalkDensity A 0 x - 1) i)^2 :=
            hctr
    _ = (1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
          * lazyChiSquareDistance A 0 x := by rw [h0]
    _ = (1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
          * ((stationaryVec A x)⁻¹ - 1) := by
            rw [lazyChiSquareDistance_zero A hd x]

/-- **The TV corollary at the intrinsic rate** — the lazy twin of
`walkDistribution_tvDistance_le_of_connected`. -/
theorem lazyWalkDistribution_tvDistance_le_of_connected
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) (t : ℕ) (x : V) :
    tvDistance (lazyWalkDistribution A t x) (stationaryVec A)
      ≤ (1/2) * Real.sqrt
          ((1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
            * ((stationaryVec A x)⁻¹ - 1)) := by
  refine (tvDistance_le_half_sqrt (stationaryVec_pos A hd)
    (sum_stationaryVec A hd)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt
      (lazyChiSquareDistance_le_of_connected A hA hnn hd hcard hconn t x))
    (by norm_num)

open Scaffold.InformationTheory in
/-- **Entropy decay, lazy twin**: `D(ν_t^L ‖ π) ≤
(1 − λ₂/2)^{2t} · ((π x)⁻¹ − 1)` at the headline's exact hypothesis
set — the delivered bridge composed with the lazy bound. -/
theorem klDiv_lazyWalkDistribution_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) (t : ℕ) (x : V) :
    klDiv (lazyWalkDistribution A t x) (stationaryVec A)
      ≤ (1 - secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
          * ((stationaryVec A x)⁻¹ - 1) :=
  (klDiv_le_sum_sq_div
      (lazyWalkDistribution_nonneg A hnn hd t x)
    (fun i => stationaryVec_pos A hd i)
    (sum_lazyWalkDistribution A hd t x)
    (sum_stationaryVec A hd)).trans
    (lazyChiSquareDistance_le_of_connected A hA hnn hd hcard hconn t x)

end SpectralGraphTheory
