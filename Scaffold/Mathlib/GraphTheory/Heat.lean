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
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Tendsto

/-!
# The heat semigroup on the graph Laplacian

Phase B, Steps 1–3 of `proposals/reversibility-and-heat-semigroup.md`
(operator gate resolved 2026-08-23: `sgt-gaps.md`, from the independent
`spectral-proof` clean-sheet rewrite project, names this interface as its
one remaining Scaffold dependency). The continuous-time diffusion object
`e^{-tL}` on the combinatorial Laplacian, at the matrix level — the
standard "diffusion on a graph" operator (Chung, *Spectral Graph
Theory*, ch. 1; Grigor'yan, *Introduction to Analysis on Graphs*, ch. 3)
and the continuous-time counterpart of the walk-power decay machinery of
`GraphTheory.Mixing`.

Step 1 delivers the definition and its two basic structural facts:

- `heatKernel A t = NormedSpace.exp ℝ (-(t • laplacian A))`, the heat
  evolution operator specialized to `laplacian A`;
- `heatKernel_isSymm`: on symmetric input the heat kernel is symmetric
  for every time — through the pin's `Matrix.IsSymm.exp` applied to the
  negated scalar multiple of the (symmetric) Laplacian;
- `heatKernel_zero`: at time zero the semigroup is the identity.

Step 2 delivers the semigroup law:

- `heatKernel_mul_heatKernel`: `heatKernel A s * heatKernel A t =
  heatKernel A (s + t)` — through the pin's
  `Matrix.exp_add_of_commute`, whose commuting pair is the two negated
  scalar multiples of `laplacian A` (scalar multiples of one matrix
  commute). No symmetry hypothesis: the law is hypothesis-free, as the
  consumer's diffusion interface expects.

Also here: `exp_eq_one_add_of_mul_self_eq_zero`, the general
square-zero-matrix exponential collapse `exp M = 1 + M` when
`M * M = 0` — the closed-form handle that makes the QA fixtures (and any
nilpotent-index-2 perturbation computation) exactly evaluable — with its
time-parametrized corollary `exp_neg_smul_eq_one_add_of_mul_self_eq_zero`
(`exp (-(t • M)) = 1 + -(t • M)` at every `t`, the exponent squaring to
`(t * t) • (M * M) = 0`).

Step 3 delivers mass conservation:

- `heatKernel_mulVec_onesVec`: `heatKernel A t *ᵥ onesVec = onesVec`
  at every time — heat diffusing on the graph neither creates nor
  destroys total heat — hypothesis-free, through the shelf's
  `laplacian_ones_in_kernel` (`L *ᵥ 1 = 0` needs no symmetry).

The Step-3 engine, all of it reusable and norm-free (the entrywise /
Pi topology only):

- `expSeries_hasSum_exp`: the exponential series `∑ n!⁻¹ • Mⁿ`
  converges to `NormedSpace.exp ℝ M` in the entrywise topology — the
  matrix-level summability content the pin's normed-section lemmas do
  not provide at matrix type (see the survey note below);
- `exp_mulVec_eq_of_mulVec_eq_zero`: whenever `M *ᵥ v = 0`, the
  exponential fixes `v` (`exp ℝ M *ᵥ v = v`) — mass conservation for
  *any* Laplacian-harmonic vector, not just `onesVec`;
- the entrywise power bound `abs_pow_apply_le` (`|Mⁿ i j| ≤ Bⁿ` at
  `B = ∑ |M p q|`), the entrywise summability `summable_exp_term`, and
  the pin-gap helper `hasSum_pi`.

All statements are proved hard crust; this module adds no axioms.

Step 4 (the payoff statement) delivers eigenmode decay and the
connected-graph DC limit:

- `heatKernel_mulVec_eigvecOf`: every eigenbasis vector of `laplacian A`
  is an eigenvector of `heatKernel A t` with eigenvalue
  `Real.exp (-(t * λᵢ))` — the mode-`i` decay factor — through the
  eigenmode engine below (Step 3's convergence machinery applied to an
  eigenvector, the load-bearing connection the plan asked for);
- `heatKernel_decayFactor_antitone` / `heatKernel_decayFactor_le_one`:
  for sorted eigenvalues and `0 ≤ t`, higher frequencies dissipate at
  least as fast as lower ones, and (PSD input) every factor is at most
  `1` — dissipation, not growth;
- `heatKernel_mulVec_eq_sum`: the eigenbasis expansion of the heat
  action — `heatKernel A t *ᵥ x` resolved over the proved orthonormal
  eigenbasis with damped coefficients, the spectral-calculus identity of
  the proposal in action form;
- `heatKernel_mulVec_tendsto_atTop`: on a connected graph, free
  diffusion leaves only the DC component — the heat flow of any initial
  vector converges to its mean, `((∑ j, x j) / |V|) • onesVec`.

The two engines are reusable general matrix lemmas: the eigenmode engine
`exp_mulVec_eq_smul_of_mulVec_eq_smul` (`M *ᵥ v = μ • v → exp ℝ M *ᵥ v =
Real.exp μ • v`, Step 3's kernel engine is its `μ = 0` case) and the
rank-one-idempotent collapse `exp_eq_one_add_of_mul_self_eq_smul`
(`M * M = c • M → exp ℝ M = 1 + ((exp c - 1)/c) • M`, the `c = 0`
square-zero collapse's sibling — the closed form that makes the
symmetric `K₂` fixture exactly evaluable at symbolic times).

## Scope notes (recorded before stating, 2026-08-23)

- `t` ranges over all of ℝ by construction. For negative `t` this is
  the *growing* (backward) semigroup — the same caveat
  `Perturbation.Duhamel` documents for its vector-level damped expansion.
  The decay statements (Steps 2–4) carry `0 ≤ t` where they need it.
- `heatKernel` is defined for *every* real matrix `A`; symmetry of the
  kernel is stated under `A.IsSymm` (via `laplacian_symmetric`), which is
  load-bearing: QA exhibits an asymmetric matrix whose heat kernel is
  provably not symmetric at `t = 1`.
- This is the *matrix-level* semigroup. The vector-level damped
  eigenbasis expansion `Perturbation.Duhamel.heatApply` is a different
  representation of the same dynamics; connecting the two is the
  eigenbasis-decay step's (Step 4) business, not Step 1's.

## Naming note

The pinned Mathlib has no `Matrix.exp` declaration: the exponential is
`NormedSpace.exp` applied at matrix type, and the matrix-namespaced
lemmas (`Matrix.IsSymm.exp`, `Matrix.exp_add_of_commute`, …) are
wrappers that hide the (non-canonical) matrix norm inside their proofs.
The Step-0 survey is recorded in the proposal.

## Step-3 survey note (recorded before proving, 2026-08-23)

`NormedSpace.exp` at this pin is defined in the *topological-algebra*
section of `Analysis/Normed/Algebra/Exponential.lean` (a `T2`
topological ring over a field — no norm), which is why the statements
above elaborate with the entrywise (Pi) topology that
`Topology/Instances/Matrix.lean` puts on matrices. The pin's
`expSeries_summable'` lives in the *normed* `CompleteAlgebra` section,
so it does not apply at matrix type without `letI`-ing the `linftyOp`
norm — and its summability would then live in the linftyOp-induced
topology, with no topology-transfer lemma available at this pin. The
pin also has **no Pi-type `HasSum`/`Summable` lemmas** at all. Step 3
therefore establishes everything entrywise: the power bound
`abs_pow_apply_le`, comparison against
`Real.summable_pow_div_factorial`, the pin-gap helper `hasSum_pi`
(assembled from `Filter.tendsto_pi_nhds` + `Finset.sum_apply`), and the
`HasSum.map` push through the continuous additive action
`N ↦ N *ᵥ v` — the same pattern the pin's own `Matrix.transpose_tsum`
uses for its tsum commutation.
-/

namespace SpectralGraphTheory

open Matrix Filter

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Square-zero exponential collapse
-/

/-- The exponential of a square-zero matrix collapses to `1 + M`: every
power from the second on vanishes, so the defining series
`∑ n!⁻¹ • Mⁿ` sums over `{0, 1}` only. General (no symmetry or graph
hypotheses); the closed form QA uses to evaluate heat kernels exactly
whenever the exponent is square-zero. -/
theorem exp_eq_one_add_of_mul_self_eq_zero (M : Matrix V V ℝ)
    (hM : M * M = 0) :
    NormedSpace.exp ℝ M = 1 + M := by
  rw [NormedSpace.exp_eq_tsum]
  show ∑' n : ℕ, ((Nat.factorial n : ℝ)⁻¹) • M ^ n = 1 + M
  have hz : ∀ n ∉ Finset.range 2, ((Nat.factorial n : ℝ)⁻¹) • M ^ n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, pow_two, hM, zero_mul, smul_zero]
  rw [tsum_eq_sum hz, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp

/-- The square-zero collapse at *every* time: `exp (-(t • M)) =
1 + -(t • M)` whenever `M * M = 0`, since the exponent squares to
`(t * t) • (M * M) = 0`. The closed form behind every-time evaluation of
heat kernels on square-zero-Laplacian fixtures (QA), and available for
any nilpotent-index-2 perturbation computation. -/
theorem exp_neg_smul_eq_one_add_of_mul_self_eq_zero (M : Matrix V V ℝ)
    (hM : M * M = 0) (t : ℝ) :
    NormedSpace.exp ℝ (-(t • M)) = 1 + -(t • M) := by
  refine exp_eq_one_add_of_mul_self_eq_zero _ ?_
  rw [neg_mul_neg, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
    hM, smul_zero]

/-!
## The heat semigroup, Step 1: definition and basic structure
-/

/-- The heat semigroup on the combinatorial Laplacian: the matrix
exponential `e^{-tL}` of `-(t • laplacian A)`. For `0 ≤ t` this is
diffusion on the graph `A`; for negative `t` it is the growing backward
semigroup (see the scope notes above). Total in `A` and `t`; no
symmetry hypothesis is needed to *state* it. -/
noncomputable def heatKernel (A : WAdj (V := V)) (t : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp ℝ (-(t • laplacian A))

/-- On a symmetric network the heat kernel is symmetric at every time:
the Laplacian is symmetric (`laplacian_symmetric`), negation and scalar
multiplication preserve symmetry, and the pinned Mathlib's
`Matrix.IsSymm.exp` transfers it through the exponential. -/
theorem heatKernel_isSymm (A : WAdj (V := V)) (hA : A.IsSymm) (t : ℝ) :
    (heatKernel A t).IsSymm :=
  ((laplacian_symmetric A hA).smul t).neg |>.exp ℝ

/-- The heat semigroup is the identity at time zero: `-0 • L = 0` and
`NormedSpace.exp_zero`. Hypothesis-free — it holds for every matrix,
symmetric or not. -/
theorem heatKernel_zero (A : WAdj (V := V)) : heatKernel A 0 = 1 := by
  rw [heatKernel, zero_smul, neg_zero, NormedSpace.exp_zero]

/-!
## The heat semigroup, Step 2: the semigroup law
-/

/-- **The semigroup property**: flowing for time `s` and then time `t` is
flowing for time `s + t`. Hypothesis-free — no symmetry, no sign
restriction on the times (for negative times this is the backward/growing
semigroup, per the scope notes above). Route: the two exponents
`-(s • laplacian A)` and `-(t • laplacian A)` are scalar multiples of one
matrix, hence commute (`(s • L) * (t • L) = (s * t) • (L * L)` both
ways), so the pin's `Matrix.exp_add_of_commute` applies — its wrapper
`letI`s the `linftyOp` norm inside its own proof, so no norm or
ball-membership hypothesis reaches this statement (the Step-0 survey's
finding); the joined exponent reduces by `neg_add` + `add_smul`. -/
theorem heatKernel_mul_heatKernel (A : WAdj (V := V)) (s t : ℝ) :
    heatKernel A s * heatKernel A t = heatKernel A (s + t) := by
  have hcomm : Commute (-(s • laplacian A)) (-(t • laplacian A)) := by
    show (- (s • laplacian A)) * (- (t • laplacian A))
      = (- (t • laplacian A)) * (- (s • laplacian A))
    rw [neg_mul_neg, neg_mul_neg, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      smul_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
      mul_comm s t]
  have h := Matrix.exp_add_of_commute ℝ (-(s • laplacian A)) (-(t • laplacian A))
    hcomm
  simp only [heatKernel] at h ⊢
  rw [← h]
  congr 1
  rw [← neg_add, ← add_smul]

/-!
## Entrywise series tools (Step 3 infrastructure)
-/

/-- The pin-gap Pi `HasSum` assembler: a family into a Pi type has sum
`a` whenever every entrywise family has sum `a x`. Assembled from
`Filter.tendsto_pi_nhds` and `Finset.sum_apply` because the pinned
Mathlib carries no `hasSum_pi`/`summable_pi` lemmas at all. General
(no matrix content); the consumer is the entrywise treatment of the
exponential series below, and any future Pi-typed series argument. -/
theorem hasSum_pi {ι : Type} {δ : Type} {β : δ → Type}
    [∀ x : δ, AddCommMonoid (β x)] [∀ x : δ, TopologicalSpace (β x)]
    {f : ι → ∀ x : δ, β x} {a : ∀ x : δ, β x}
    (h : ∀ x, HasSum (fun n => f n x) (a x)) : HasSum f a := by
  show Filter.Tendsto (fun s : Finset ι => ∑ n ∈ s, f n) Filter.atTop (nhds a)
  rw [tendsto_pi_nhds]
  intro x
  exact (Filter.tendsto_congr (fun s => Finset.sum_apply x s f)).mpr (h x)

/-- Entrywise power bound: every entry of `Mⁿ` is at most the `n`-th
power of the total mass `B := ∑ p q, |M p q|`. Induction through
`Matrix.mul_apply`; the base case is the identity's indicator. This is
the entire "matrix analysis" input to the summability of the
exponential series — crude, but exactly evaluable and norm-free. -/
theorem abs_pow_apply_le (M : Matrix V V ℝ) (n : ℕ) (i j : V) :
    |(M ^ n) i j| ≤ (∑ p, ∑ q, |M p q|) ^ n := by
  induction n generalizing i j with
  | zero =>
    simp only [pow_zero]
    rw [Matrix.one_apply]
    split <;> simp
  | succ m ih =>
    have hcol : ∑ k, |M k j| ≤ ∑ p, ∑ q, |M p q| := by
      have h1 : ∀ p : V, |M p j| ≤ ∑ q, |M p q| := by
        intro p
        have hsplit : ∑ q, |M p q| = |M p j| + ∑ q ∈ Finset.univ.erase j, |M p q| := by
          rw [← Finset.sum_insert (f := fun q => |M p q|)
            (Finset.not_mem_erase j Finset.univ),
            Finset.insert_erase (Finset.mem_univ j)]
        rw [hsplit]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun q _ => abs_nonneg _)
      exact Finset.sum_le_sum (f := fun p => |M p j|) (g := fun p => ∑ q, |M p q|)
        (fun p _ => h1 p)
    have hB : (0:ℝ) ≤ ∑ p, ∑ q, |M p q| :=
      Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg _
    rw [pow_succ, Matrix.mul_apply]
    calc |∑ k, (M ^ m) i k * M k j|
        ≤ ∑ k, |(M ^ m) i k * M k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |(M ^ m) i k| * |M k j| := by simp [abs_mul]
      _ ≤ ∑ k, (∑ p, ∑ q, |M p q|) ^ m * |M k j| :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (ih i k) (abs_nonneg _)
      _ = (∑ p, ∑ q, |M p q|) ^ m * ∑ k, |M k j| := by rw [Finset.mul_sum]
      _ ≤ (∑ p, ∑ q, |M p q|) ^ m * ∑ p, ∑ q, |M p q| :=
          mul_le_mul_of_nonneg_left hcol (pow_nonneg hB m)
      _ = (∑ p, ∑ q, |M p q|) ^ (m + 1) := by rw [pow_succ]

/-- Every entry of the exponential series is summable, by comparison
with `B ^ n / n!` (whose sum is `e ^ B`) through the power bound above.
The `ℝ`-level summability that the assembled matrix statement
`expSeries_hasSum_exp` consumes. -/
theorem summable_exp_term (M : Matrix V V ℝ) (i j : V) :
    Summable fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * (M ^ n) i j := by
  refine Summable.of_norm_bounded _ (Real.summable_pow_div_factorial (∑ p, ∑ q, |M p q|)) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (abs_pow_apply_le M n i j) (by positivity)

/-- The exponential series of a finite real matrix converges, in the
entrywise (Pi) topology, to `NormedSpace.exp ℝ M`. This is the
matrix-level summability content that the pinned Mathlib's
`NormedSpace.expSeries_hasSum_exp` does *not* provide at matrix type:
that lemma lives in the normed `CompleteAlgebra` section, and applying
it would require `letI`-ing a matrix norm whose induced topology is not
transferable to the entrywise one at this pin. Assembled from
entrywise summability (`summable_exp_term`) and the pin-gap `hasSum_pi`
(twice, for the two Pi levels of `V → V → ℝ`). -/
theorem expSeries_hasSum_exp (M : Matrix V V ℝ) :
    HasSum (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ • M ^ n) (NormedSpace.exp ℝ M) := by
  have hentry : ∀ i : V, HasSum (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹ • M ^ n) i)
      (fun j => ∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * (M ^ n) i j) := by
    intro i
    exact hasSum_pi fun j => (summable_exp_term M i j).hasSum
  have key : HasSum (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ • M ^ n)
      (Matrix.of fun i j => ∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * (M ^ n) i j) :=
    hasSum_pi hentry
  have hE : NormedSpace.exp ℝ M
      = Matrix.of fun i j => ∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * (M ^ n) i j := by
    rw [NormedSpace.exp_eq_tsum]
    exact key.tsum_eq
  rw [hE]
  exact key

/-!
## The heat semigroup, Step 3: mass conservation (with the generalized
eigenmode engine of Step 4)
-/

/-- Family transport for `HasSum` along a pointwise equality of the
summed families. The pin carries no `HasSum.congr`; this two-line
funext wrapper is the honest replacement, consumed by the eigenmode
engine below and the `M * M = c • M` collapse. -/
private theorem hasSum_of_eq {ι : Type} {M : Type} [AddCommMonoid M]
    [TopologicalSpace M] {f g : ι → M} {a : M} (h : ∀ n, f n = g n)
    (hs : HasSum f a) : HasSum g a := by
  have h1 : f = g := funext h
  rw [h1] at hs
  exact hs

/-- Powers of a matrix act on an eigenvector by powers of the
eigenvalue: `(M ^ n) *ᵥ v = (μ ^ n) • v` whenever `M *ᵥ v = μ • v`. The
`pow_add` + `Matrix.mulVec_mulVec` induction (this pin's `pow_succ'`
factors the wrong way for the `M ^ n * M` split; see the proposal's
technique notes). -/
theorem pow_mulVec_smul (M : Matrix V V ℝ) {v : V → ℝ} {μ : ℝ}
    (hM : M *ᵥ v = μ • v) (n : ℕ) : (M ^ n) *ᵥ v = (μ ^ n) • v := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [show M ^ (m + 1) = M ^ m * M by rw [pow_add, pow_one],
      ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, ih, smul_smul,
      ← pow_succ']

/-- **The eigenmode engine**: whenever `M *ᵥ v = μ • v`, the
exponential acts on `v` by the scalar exponential,
`exp ℝ M *ᵥ v = Real.exp μ • v`. The route is Step 3's bridge applied
to an eigenvector: the series `HasSum` `expSeries_hasSum_exp` is pushed
through the continuous additive action `N ↦ N *ᵥ v` (`HasSum.map`, the
same pattern as `exp_mulVec_eq_of_mulVec_eq_zero`, whose statement is
the `μ = 0` case of this one), every series term collapses by
`pow_mulVec_smul`, and the remaining scalar series is summed by the
pin's `NormedSpace.exp_series_hasSum_exp'` at ℝ (identified with
`Real.exp` through `Real.exp_eq_exp_ℝ` — the pin's normed-section lemma
applies at the scalar level, where no matrix-type transfer is needed). -/
theorem exp_mulVec_eq_smul_of_mulVec_eq_smul (M : Matrix V V ℝ) (v : V → ℝ)
    (μ : ℝ) (hM : M *ᵥ v = μ • v) :
    (NormedSpace.exp ℝ M) *ᵥ v = (Real.exp μ) • v := by
  have hT : Continuous fun N : Matrix V V ℝ => N *ᵥ v := by
    refine continuous_pi fun i => ?_
    have h : Continuous fun N : V → V → ℝ => ∑ j, N i j * v j := by
      refine continuous_finset_sum _ fun j _ => ?_
      have hij : Continuous fun N : V → V → ℝ => N i j :=
        (continuous_apply j).comp (continuous_apply i)
      exact hij.mul continuous_const
    simpa only [Matrix.mulVec, Matrix.dotProduct] using h
  have hmap := (expSeries_hasSum_exp M).map
    ({ toFun := fun N => N *ᵥ v
       map_zero' := Matrix.zero_mulVec v
       map_add' := fun N₁ N₂ => Matrix.add_mulVec N₁ N₂ v } :
      Matrix V V ℝ →+ (V → ℝ)) hT
  have hterm : ∀ n : ℕ, ((Nat.factorial n : ℝ)⁻¹ • M ^ n) *ᵥ v
      = ((Nat.factorial n : ℝ)⁻¹ * μ ^ n) • v := by
    intro n
    rw [Matrix.smul_mulVec_assoc, pow_mulVec_smul M hM n, smul_smul]
  have hμexp : Real.exp μ = NormedSpace.exp ℝ μ := by rw [Real.exp_eq_exp_ℝ]
  have hscal : HasSum (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * μ ^ n)
      (NormedSpace.exp ℝ μ) := by
    simpa [smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) μ
  have hsmulT : Continuous fun r : ℝ => r • v := by
    refine continuous_pi fun i => ?_
    simpa [Pi.smul_apply, smul_eq_mul] using continuous_id.mul continuous_const
  have hscal' : HasSum (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹ * μ ^ n) • v)
      ((NormedSpace.exp ℝ μ) • v) :=
    hscal.map
      ({ toFun := fun r : ℝ => r • v
         map_zero' := zero_smul _ v
         map_add' := fun a b => add_smul a b v } : ℝ →+ (V → ℝ)) hsmulT
  have hgoal : (NormedSpace.exp ℝ M) *ᵥ v
      = ∑' n : ℕ, (((Nat.factorial n : ℝ)⁻¹ • M ^ n) *ᵥ v) :=
    hmap.tsum_eq.symm
  rw [hgoal, tsum_congr hterm]
  exact hscal'.tsum_eq.trans (by rw [hμexp])

/-- **Mass conservation for kernel vectors**: whenever `M *ᵥ v = 0`,
the exponential of `M` fixes `v`. Route: the additive action
`N ↦ N *ᵥ v` is continuous (entrywise finite sums of coordinate
projections), so it pushes `expSeries_hasSum_exp` through
`HasSum.map`; every series term with `n ≥ 1` annihilates `v` because
`(M ^ n * M) *ᵥ v = M ^ n *ᵥ (M *ᵥ v) = 0` (`pow_add` +
`Matrix.mulVec_mulVec`), so the pushed series collapses onto its
`n = 0` term, which is `v`. Hypothesis-free beyond the kernel
equation itself. The `μ = 0` case of the eigenmode engine
`exp_mulVec_eq_smul_of_mulVec_eq_smul`. -/
theorem exp_mulVec_eq_of_mulVec_eq_zero (M : Matrix V V ℝ) (v : V → ℝ)
    (hM : M *ᵥ v = 0) : (NormedSpace.exp ℝ M) *ᵥ v = v := by
  have h := exp_mulVec_eq_smul_of_mulVec_eq_smul M v 0
    (by rw [hM, zero_smul])
  simpa using h

/-- **Mass conservation for the heat semigroup** (Step 3): diffusing
heat on a graph neither creates nor destroys it — the all-ones vector
is a fixed point of `heatKernel A t` at every time. Hypothesis-free:
`laplacian_ones_in_kernel` (`L *ᵥ 1 = 0`) needs no symmetry, because
the Laplacian's row sums vanish identically (`deg i - ∑ j A i j = 0`).
Together with Steps 1–2 this is the diffusion interface's third core
item: identity, semigroup law, and mass preservation. -/
theorem heatKernel_mulVec_onesVec (A : WAdj (V := V)) (t : ℝ) :
    heatKernel A t *ᵥ onesVec = onesVec := by
  rw [heatKernel]
  refine exp_mulVec_eq_of_mulVec_eq_zero _ _ ?_
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, laplacian_ones_in_kernel,
    smul_zero, neg_zero]

/-!
## The heat semigroup, Step 4: eigenmode decay and the DC limit
-/

/-- The scalar decay-factor asymptotics: for `0 < μ`, the mode factor
`Real.exp (-(t * μ))` vanishes as `t → ∞` (`Real.tendsto_exp_atBot`
composed with the linear escape `t ↦ μ * t` to `-∞`). The per-mode
input of the DC limit below, and of any future mixing statement. -/
theorem tendsto_exp_neg_mul_atTop {μ : ℝ} (hμ : 0 < μ) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(t * μ))) Filter.atTop
      (nhds 0) := by
  have h1 : Filter.Tendsto (fun t : ℝ => μ * t) Filter.atTop Filter.atTop :=
    tendsto_id.const_mul_atTop hμ
  have h2 : Filter.Tendsto (fun t : ℝ => -(μ * t)) Filter.atTop Filter.atBot :=
    tendsto_neg_atTop_atBot.comp h1
  exact Real.tendsto_exp_atBot.comp (h2.congr fun t => by ring)

/-- **The rank-one-idempotent exponential collapse**: if `M * M = c • M`
with `c ≠ 0`, then `exp ℝ M = 1 + ((exp c - 1)/c) • M`. Every power
from the first on is a scalar multiple of `M` (`M ^ n = c ^ (n-1) • M`),
so the defining series splits into the constant term and a rescaled
scalar exponential tail; the tail is shifted by the pin's topological-
group lemma `hasSum_nat_add_iff'` (the pin has no plain tail-shift
`HasSum` lemma), divided through by `c` via a continuous additive map,
and reassembled with `tsum_eq_zero_add` + `tsum_smul_const` — all on
top of Step 3's `expSeries_hasSum_exp`. The `M * M = 0` collapse
`exp_eq_one_add_of_mul_self_eq_zero` is the `c = 0` sibling; this is
the closed form that makes the symmetric `K₂` fixture (whose Laplacian
squares to `2 • L`) exactly evaluable at symbolic times. -/
theorem exp_eq_one_add_of_mul_self_eq_smul (M : Matrix V V ℝ) {c : ℝ}
    (hc : c ≠ 0) (hM : M * M = c • M) :
    NormedSpace.exp ℝ M = 1 + ((Real.exp c - 1) / c) • M := by
  have hpow : ∀ n : ℕ, M ^ (n + 1) = (c ^ n) • M := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [show M ^ (m + 1 + 1) = M ^ (m + 1) * M by rw [pow_add, pow_one],
        ih, smul_mul_assoc, hM, smul_smul, pow_succ]
  have hcexp : Real.exp c = NormedSpace.exp ℝ c := by rw [Real.exp_eq_exp_ℝ]
  have hscal : HasSum (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * c ^ n)
      (NormedSpace.exp ℝ c) := by
    simpa [smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) c
  have h1 : HasSum (fun n : ℕ => (Nat.factorial (n + 1) : ℝ)⁻¹ * c ^ (n + 1))
      (Real.exp c - 1) := by
    have h2 := (hasSum_nat_add_iff'
      (f := fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * c ^ n) (k := 1)
      (g := NormedSpace.exp ℝ c)).2 hscal
    rw [hcexp]
    simpa [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      pow_zero, inv_one, mul_one, zero_add] using h2
  have h2 : HasSum (fun n : ℕ => ((Nat.factorial (n + 1) : ℝ)⁻¹ * c ^ (n + 1)) * c⁻¹)
      ((Real.exp c - 1) / c) := by
    rw [div_eq_mul_inv]
    exact h1.map
      ({ toFun := fun r : ℝ => r * c⁻¹
         map_zero' := zero_mul c⁻¹
         map_add' := fun a b => add_mul a b c⁻¹ } : ℝ →+ ℝ)
      (continuous_id.mul continuous_const)
  have hpt : ∀ n : ℕ, ((Nat.factorial (n + 1) : ℝ)⁻¹ * c ^ (n + 1)) * c⁻¹
      = (Nat.factorial (n + 1) : ℝ)⁻¹ * c ^ n := by
    intro n
    rw [pow_succ, mul_assoc, mul_inv_cancel_right₀ hc]
  have htail : HasSum (fun n : ℕ => (Nat.factorial (n + 1) : ℝ)⁻¹ * c ^ n)
      ((Real.exp c - 1) / c) := hasSum_of_eq hpt h2
  have hgsm := htail.summable
  have hkey : ∑' n : ℕ, (Nat.factorial (n + 1) : ℝ)⁻¹ • M ^ (n + 1)
      = ((Real.exp c - 1) / c) • M := by
    have h1' : ∑' n : ℕ, ((Nat.factorial (n + 1) : ℝ)⁻¹ * c ^ n) • M
        = ((Real.exp c - 1) / c) • M := by
      rw [← htail.tsum_eq]
      exact tsum_smul_const hgsm M
    rw [← h1']
    exact tsum_congr fun n => by rw [hpow n, smul_smul]
  rw [NormedSpace.exp_eq_tsum]
  show ∑' n : ℕ, ((Nat.factorial n : ℝ)⁻¹ • M ^ n)
      = 1 + ((Real.exp c - 1) / c) • M
  rw [tsum_eq_zero_add (expSeries_hasSum_exp M).summable]
  have hf0 : ((Nat.factorial 0 : ℝ)⁻¹ • M ^ (0 : ℕ)) = 1 := by simp
  rw [hf0]
  have hbeta : ∑' b : ℕ,
        (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ • M ^ n) (b + 1)
      = ∑' n : ℕ, (Nat.factorial (n + 1) : ℝ)⁻¹ • M ^ (n + 1) := rfl
  rw [hbeta, hkey]

/-- **Eigenmode decay** (Step 4, mode form): every eigenbasis vector of
`laplacian A` is an eigenvector of the heat kernel at *every* time,
with eigenvalue the mode's decay factor `Real.exp (-(t * λᵢ))` — the
precise sense in which diffusion damps each graph frequency separately.
Route: the eigenmode engine `exp_mulVec_eq_smul_of_mulVec_eq_smul` at
the eigenvector equation `mulVec_eigenvectorBasis`, the exponent's
scalar action assembled by `smul_smul`/`neg_smul`. This is Step 3's
convergence machinery applied to an eigenvector — the load-bearing
bridge the plan required, not a parallel construction beside it. -/
theorem heatKernel_mulVec_eigvecOf (A : WAdj (V := V)) (hA : A.IsSymm)
    (t : ℝ) (i : V) :
    heatKernel A t *ᵥ eigvecOf (laplacian A) (laplacian_symmetric A hA) i
      = Real.exp (-(t * eigvalOf (laplacian A) (laplacian_symmetric A hA) i))
        • eigvecOf (laplacian A) (laplacian_symmetric A hA) i := by
  rw [heatKernel]
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  have hev : laplacian A *ᵥ eigvecOf (laplacian A) (laplacian_symmetric A hA) i
      = eigvalOf (laplacian A) (laplacian_symmetric A hA) i
        • eigvecOf (laplacian A) (laplacian_symmetric A hA) i :=
    (isHermitian_of_isSymm (laplacian_symmetric A hA)).mulVec_eigenvectorBasis i
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, hev, smul_smul, neg_smul]

/-- **Decay-factor monotonicity** (Step 4): for sorted eigenvalues
`λᵢ ≤ λⱼ` and `t ≥ 0`, the mode-`j` decay factor is at most the
mode-`i` factor — higher graph frequencies dissipate at least as fast
as lower ones. Purely scalar: `evals_sorted` + `Real.exp_le_exp` +
monotonicity of multiplication by `t ≥ 0`. -/
theorem heatKernel_decayFactor_antitone (A : WAdj (V := V)) (hA : A.IsSymm)
    {t : ℝ} (ht : 0 ≤ t) {i j : Fin (Fintype.card V)} (hij : i ≤ j) :
    Real.exp (-(t * evals (laplacian_symmetric A hA) j))
      ≤ Real.exp (-(t * evals (laplacian_symmetric A hA) i)) := by
  apply Real.exp_le_exp.2
  exact neg_le_neg (mul_le_mul_of_nonneg_left (evals_sorted _ hij) ht)

/-- **Every decay factor dissipates** (Step 4): on symmetric-nonnegative
input the Laplacian is PSD (`laplacian_psd`), so every sorted
eigenvalue is nonnegative (`evals_mem_eigvalOf` +
`quadForm_eigvecOf_self`) and every mode factor is at most `1` at
`t ≥ 0` — the heat semigroup genuinely damps every mode, never
amplifies one. -/
theorem heatKernel_decayFactor_le_one (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) {t : ℝ} (ht : 0 ≤ t)
    (k : Fin (Fintype.card V)) :
    Real.exp (-(t * evals (laplacian_symmetric A hA) k)) ≤ 1 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf (laplacian_symmetric A hA) k
  have hge : 0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) i := by
    rw [← quadForm_eigvecOf_self (laplacian_symmetric A hA) i]
    exact laplacian_psd A hA hnonneg _
  rw [hi]
  calc Real.exp (-(t * eigvalOf (laplacian A) (laplacian_symmetric A hA) i))
      ≤ Real.exp 0 := Real.exp_le_exp.2
        (by rw [neg_nonpos]; exact mul_nonneg ht hge)
    _ = 1 := by rw [Real.exp_zero]

/-- **The eigenbasis expansion of the heat action** (Step 4, the
spectral-calculus identity in action form): every input vector is
resolved over the proved orthonormal eigenbasis of `laplacian A`, each
component damped by its own mode factor —
`heatKernel A t *ᵥ x = ∑ᵢ e^{-t·λᵢ} (vᵢ ⬝ᵥ x) • vᵢ`. Route: the input
is expanded by the shelf's entrywise completeness
`eigvecOf_expansion_apply`, the (linear) heat action commutes with the
finite sum through `Matrix.mulVecLin`, and each eigenbasis component is
damped by `heatKernel_mulVec_eigvecOf`. -/
theorem heatKernel_mulVec_eq_sum (A : WAdj (V := V)) (hA : A.IsSymm)
    (t : ℝ) (x : V → ℝ) :
    heatKernel A t *ᵥ x
      = ∑ i, (Real.exp (-(t * eigvalOf (laplacian A)
            (laplacian_symmetric A hA) i))
          * Matrix.dotProduct (eigvecOf (laplacian A)
            (laplacian_symmetric A hA) i) x)
          • eigvecOf (laplacian A) (laplacian_symmetric A hA) i := by
  have hx : x = ∑ i, Matrix.dotProduct
      (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) x
      • eigvecOf (laplacian A) (laplacian_symmetric A hA) i := by
    funext a
    rw [Finset.sum_apply]
    exact (eigvecOf_expansion_apply (laplacian_symmetric A hA) x a).symm
  rw [show heatKernel A t *ᵥ x = Matrix.mulVecLin (heatKernel A t) x
      from rfl]
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul,
    heatKernel_mulVec_eigvecOf A hA t i, smul_smul, mul_comm]

omit [DecidableEq V] in
/-- The all-ones pairing helper: `(c • onesVec) ⬝ᵥ (d • onesVec)` is
`c * d * |V|`. Both smuls resolved by `dotProduct_smul_onesVec'`-style
entrywise arithmetic. Private to the DC-limit proof. -/
private theorem dotProduct_smul_onesVec_smul (c d : ℝ) :
    Matrix.dotProduct (c • onesVec (V := V)) (d • onesVec)
      = c * d * (Fintype.card V : ℝ) := by
  simp only [Matrix.dotProduct, Pi.smul_apply, onesVec, smul_eq_mul, mul_one,
    one_mul, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  ring

omit [DecidableEq V] in
/-- The one-sided pairing helper: `(c • onesVec) ⬝ᵥ x = c * ∑ j, x j`. -/
private theorem dotProduct_smul_onesVec' (c : ℝ) (x : V → ℝ) :
    Matrix.dotProduct (c • onesVec (V := V)) x = c * ∑ j, x j := by
  simp only [Matrix.dotProduct, Pi.smul_apply, onesVec, smul_eq_mul, mul_one,
    Finset.mul_sum]

/-- **The connected-graph DC limit** (Step 4, the proposal's payoff):
on a connected graph with symmetric nonnegative weights, free diffusion
leaves only the DC component — the heat flow of *any* initial vector
converges, as `t → ∞`, to its mean `((∑ j, x j) / |V|) • onesVec`.

Route (every piece load-bearing on the shelf's spectral center):
PSD bounds every eigenvalue below (`quadForm_eigvecOf_self` +
`laplacian_psd`); `det L = 0` (`Matrix.exists_mulVec_eq_zero_iff` at
`onesVec`) + `det_eq_prod_eigenvalues` gives a kernel eigenmode; the
kernel characterization `laplacian_kernel_eq_span_onesVec` makes its
eigenvector a unit multiple of `onesVec`; any *second* kernel mode
would put two orthogonal unit vectors in one line — impossible — so
every other eigenvalue is strictly positive and its factor vanishes by
`tendsto_exp_neg_mul_atTop`; the eigenbasis expansion
`heatKernel_mulVec_eq_sum` turns the flow into the finite damped sum;
`tendsto_finset_sum` passes the limit through; the surviving kernel
contribution is identified with the mean through
`dotProduct_smul_onesVec'` and the unit-normalization
`c² |V| = 1`. -/
theorem heatKernel_mulVec_tendsto_atTop (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    (x : V → ℝ) :
    Filter.Tendsto (fun t : ℝ => heatKernel A t *ᵥ x) Filter.atTop
      (nhds (((∑ j, x j) / (Fintype.card V : ℝ)) • onesVec)) := by
  have hL := laplacian_symmetric A hA
  haveI : Nonempty V := hconn.nonempty
  obtain ⟨v₀⟩ : Nonempty V := ‹Nonempty V›
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have h : (0 : ℕ) < Fintype.card V := Fintype.card_pos
    exact_mod_cast h
  have hge : ∀ i, 0 ≤ eigvalOf (laplacian A) hL i := fun i => by
    rw [← quadForm_eigvecOf_self hL i]
    exact laplacian_psd A hA hnonneg _
  have hones : onesVec (V := V) ≠ 0 := by
    intro h
    have := congrFun h v₀
    simp [onesVec] at this
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : V, eigvalOf (laplacian A) hL i₀ = 0 := by
    have hdet : (laplacian A).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      exact ⟨onesVec, hones, laplacian_ones_in_kernel A⟩
    have hd0 := (isHermitian_of_isSymm hL).det_eq_prod_eigenvalues
    rw [hdet] at hd0
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hd0.symm
    exact ⟨i, hi⟩
  have hspan : ∀ i : V, eigvalOf (laplacian A) hL i = 0 →
      ∃ c : ℝ, c • onesVec = eigvecOf (laplacian A) hL i := by
    intro i hi
    have hmem : eigvecOf (laplacian A) hL i ∈
        Submodule.span ℝ ({onesVec (V := V)} : Set (V → ℝ)) := by
      rw [← laplacian_kernel_eq_span_onesVec A hA hnonneg hconn,
        LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hev : (laplacian A).mulVec (eigvecOf (laplacian A) hL i) = 0 := by
        have h := (isHermitian_of_isSymm hL).mulVec_eigenvectorBasis i
        rw [show (isHermitian_of_isSymm hL).eigenvalues i
            = eigvalOf (laplacian A) hL i from rfl, hi, zero_smul] at h
        exact h
      exact hev
    exact Submodule.mem_span_singleton.1 hmem
  obtain ⟨c, hc⟩ := hspan i₀ hi₀
  have hcc : c * c * (Fintype.card V : ℝ) = 1 := by
    have hn : Matrix.dotProduct (eigvecOf (laplacian A) hL i₀)
        (eigvecOf (laplacian A) hL i₀) = 1 := by
      simpa using eigvecOf_inner (laplacian A) hL i₀ i₀
    rw [← hc, dotProduct_smul_onesVec_smul] at hn
    exact hn
  have hcne : c ≠ 0 := by
    intro h
    rw [h] at hcc
    simp at hcc
  have hpos : ∀ i : V, i ≠ i₀ → 0 < eigvalOf (laplacian A) hL i := by
    intro i hne
    rcases lt_or_eq_of_le (hge i) with h | h
    · exact h
    · exfalso
      obtain ⟨d, hd⟩ := hspan i h.symm
      have hortho : Matrix.dotProduct (eigvecOf (laplacian A) hL i)
          (eigvecOf (laplacian A) hL i₀) = 0 := by
        have h := eigvecOf_inner (laplacian A) hL i i₀
        simp only [if_neg hne] at h
        exact h
      have hn : Matrix.dotProduct (eigvecOf (laplacian A) hL i)
          (eigvecOf (laplacian A) hL i) = 1 := by
        simpa using eigvecOf_inner (laplacian A) hL i i
      rw [← hd, ← hc, dotProduct_smul_onesVec_smul] at hortho
      rw [← hd, dotProduct_smul_onesVec_smul] at hn
      have hdne : d ≠ 0 := by
        intro h2; rw [h2] at hn; simp at hn
      rcases mul_eq_zero.1 hortho with h1 | h2
      · rcases mul_eq_zero.1 h1 with h3 | h4
        · exact hdne h3
        · exact hcne h4
      · exact absurd h2 hcard.ne'
  -- Per-mode convergence: the kernel mode is constant, every other
  -- mode's factor vanishes.
  have htermi₀ : Filter.Tendsto
      (fun t : ℝ => (Real.exp (-(t * eigvalOf (laplacian A) hL i₀))
          * Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) x)
          • eigvecOf (laplacian A) hL i₀) Filter.atTop
      (nhds (Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) x
          • eigvecOf (laplacian A) hL i₀)) := by
    have hconst : (fun t : ℝ => (Real.exp (-(t * eigvalOf (laplacian A) hL i₀))
        * Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) x)
        • eigvecOf (laplacian A) hL i₀)
        = fun _ => Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) x
          • eigvecOf (laplacian A) hL i₀ := by
      funext t
      rw [hi₀, mul_zero, neg_zero, Real.exp_zero, one_mul]
    rw [hconst]
    exact tendsto_const_nhds
  have hterm : ∀ i ∈ (Finset.univ.erase i₀ : Finset V), Filter.Tendsto
      (fun t : ℝ => (Real.exp (-(t * eigvalOf (laplacian A) hL i))
          * Matrix.dotProduct (eigvecOf (laplacian A) hL i) x)
          • eigvecOf (laplacian A) hL i) Filter.atTop (nhds 0) := by
    intro i hi
    have hne : i ≠ i₀ := (Finset.mem_erase.1 hi).1
    have h0 : Filter.Tendsto
        (fun t : ℝ => (Real.exp (-(t * eigvalOf (laplacian A) hL i))
          * Matrix.dotProduct (eigvecOf (laplacian A) hL i) x))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_exp_neg_mul_atTop (hpos i hne)).mul
        tendsto_const_nhds
    have h1 := h0.smul_const (eigvecOf (laplacian A) hL i)
    rw [zero_smul] at h1
    exact h1
  -- The flow is the damped expansion; split off the kernel mode.
  simp only [heatKernel_mulVec_eq_sum A hA]
  have hsumsplit : (fun t : ℝ => ∑ i : V,
        (Real.exp (-(t * eigvalOf (laplacian A) hL i))
          * Matrix.dotProduct (eigvecOf (laplacian A) hL i) x)
        • eigvecOf (laplacian A) hL i)
      = fun t => (Real.exp (-(t * eigvalOf (laplacian A) hL i₀))
          * Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) x)
          • eigvecOf (laplacian A) hL i₀
          + ∑ i ∈ Finset.univ.erase i₀, (Real.exp (-(t * eigvalOf
              (laplacian A) hL i))
            * Matrix.dotProduct (eigvecOf (laplacian A) hL i) x)
            • eigvecOf (laplacian A) hL i := by
    funext t
    rw [(Finset.sum_erase_add (Finset.univ : Finset V)
      (fun i => (Real.exp (-(t * eigvalOf (laplacian A) hL i))
        * Matrix.dotProduct (eigvecOf (laplacian A) hL i) x)
        • eigvecOf (laplacian A) hL i) (Finset.mem_univ i₀)).symm]
    exact add_comm _ _
  rw [hsumsplit]
  have htail : Filter.Tendsto (fun t : ℝ => ∑ i ∈ Finset.univ.erase i₀,
      (Real.exp (-(t * eigvalOf (laplacian A) hL i))
        * Matrix.dotProduct (eigvecOf (laplacian A) hL i) x)
      • eigvecOf (laplacian A) hL i) Filter.atTop (nhds 0) := by
    simpa using tendsto_finset_sum _ fun i hi => hterm i hi
  -- The surviving kernel contribution is exactly the mean vector.
  have hlim : Matrix.dotProduct (eigvecOf (laplacian A) hL i₀) x
      • eigvecOf (laplacian A) hL i₀
      = ((∑ j, x j) / (Fintype.card V : ℝ)) • onesVec := by
    rw [← hc, dotProduct_smul_onesVec', smul_smul]
    have hc2 : c * c = (Fintype.card V : ℝ)⁻¹ := by
      field_simp
      linarith
    have hprod : (c * ∑ j, x j) * c = (Fintype.card V : ℝ)⁻¹ * ∑ j, x j := by
      have e1 : (c * ∑ j, x j) * c = (c * c) * ∑ j, x j := by ring
      rw [e1, hc2]
    rw [hprod, div_eq_inv_mul]
  rw [← hlim]
  simpa using htermi₀.add htail

end SpectralGraphTheory
