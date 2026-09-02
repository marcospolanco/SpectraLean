import Scaffold.Mathlib.LinearAlgebra.PerronFrobenius
import Scaffold.Mathlib.GraphTheory.Normalized
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Stationary distributions of irreducible walks — the first
Perron–Frobenius consumer

The named follow-on of the `perron_frobenius` admission (2026-08-22,
`proposals/admit-perron-frobenius.md`; its module docstring names
"irreducible-directed-graph stationary distributions … and PageRank-style
centrality" as the obligations this discharge begins). Everything the
shelf has for stationary behaviour — `Stationary`'s detailed balance,
`Mixing`'s `stationaryVec` — lives on the *undirected* cone, where the
walk is diagonally similar to a symmetric operator. On genuinely
directed input that similarity does not exist, and the stationary
distribution is classically a Perron–Frobenius statement: it is the
positive left eigenvector of the walk at its Perron root, which for a
row-stochastic matrix is `1`.

**Hard crust since 2026-09-02** (`proposals/cesaro-stationary-existence.md`):
this module's stationary-distribution theorems are *proved*, with no
`perron_frobenius` contact, by the elementary route the admission's own
"Replacement path" note had left unpriced:

1. **Power positivity** (`exists_pow_pos_of_isIrreducible`): strong
   connectivity gives, for every index pair, a power with a strictly
   positive entry — an induction on `ReflTransGen` along the arcs,
   since the entry of a power dominates the product along any path.
2. **Existence by Cesàro averaging**
   (`exists_nonneg_stationary_of_row_stochastic`, through the
   Krylov–Bogoliubov cluster lemma
   `exists_cluster_stationary_of_orbit`): for *any* nonnegative
   row-stochastic matrix — no irreducibility — the Cesàro means
   `t⁻¹ • ∑_{s < t} (1 ᵥ* M^s)` of the orbit of `1` live in the
   compact simplex `{x | 0 ≤ x ∧ ∑ x = |V|}` (Tychonoff +
   `IsCompact.tendsto_subseq`, product topology, no metric machinery),
   and their action-defect is the telescoping remainder
   `t⁻¹ • (1 − 1 ᵥ* M^t)`, bounded entrywise by `2|V|/t → 0`; a
   subsequential cluster point is stationary by entrywise continuity.
3. **Strict positivity**: a nonzero nonnegative stationary `σ`
   satisfies `σ = σ ᵥ* M^m` for every `m`; if `σ j₀ = 0`, power
   positivity at `(i, j₀)` forces every single summand `σ i` of the
   zero to vanish, so `σ = 0` — contradiction.
4. **Uniqueness up to positive scale** (the min-ratio trick): at the
   minimizer of `j ↦ σ j / τ j` the difference `σ − c • τ` is
   nonnegative, stationary, and zero somewhere, hence zero by 3.

The axiom `perron_frobenius` itself remains admitted at its own full
statement (the rootMultiplicity and complex-domination clauses are not
touched by this route, and its own QA keeps exercising it); what
changed is its consumer state — after this module and `PageRank` were
re-proved, it has **zero non-QA consumers**. The deprecation decision
is the operator's (see `index/load_bearing_axioms.md`).

## Statement shapes (recorded in the proposal before stating)

- Stationarity is stated in Mathlib's left-action form `π ᵥ* P = π`
  (`Matrix.vecMul`), one `Matrix.mulVec_transpose` away from the
  eigenvector form the proof works in.
- `hdeg : ∀ i, 0 < deg A i` is a hypothesis (it is implied by
  `hnn + hirr + 2 ≤ card V`, but deriving it is plumbing; the shelf's
  own row-stochasticity interface takes it).
- Uniqueness is among *nonnegative* stationary distributions, with
  strict positivity derived (`stationaryVec_pos_of_irreducible`: no
  stationary vector of an irreducible chain can vanish anywhere).
- Nothing about rates or convergence: geometric convergence needs
  primitivity, which is a strictly stronger hypothesis (the
  `strict_dominance_refuted_QA` imprimitivity fence in the
  Perron–Frobenius QA).

## Support lemmas

Two small `Relation.ReflTransGen` congruence facts absent from the
pinned Mathlib are private: a relation congruence (the pin has `mono`
for `ReflGen` only) and the flipped-closure transfer behind
`isIrreducible_transpose`.

Delivered 2026-08-24 (`proposals/irreducible-stationary-distributions.md`);
re-proved without axiom contact 2026-09-02
(`proposals/cesaro-stationary-existence.md`).
-/

open scoped Matrix Topology

namespace SpectralGraphTheory

open Matrix Filter

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Relation congruence for the reflexive-transitive closure: a
pointwise implication of relations lifts to the closures. The pinned
Mathlib has this for `ReflGen` (`ReflGen.mono`) but not for
`ReflTransGen`. Private support for `walkTransitionMatrix_isIrreducible`. -/
private theorem reflTransGen_congr {α : Type} {r s : α → α → Prop}
    (h : ∀ a b, r a b → s a b) {i j : α} (hr : Relation.ReflTransGen r i j) :
    Relation.ReflTransGen s i j := by
  induction hr with
  | refl => exact .refl
  | @tail b c _ hstep ih => exact ih.tail (h _ _ hstep)

/-- The reflexive-transitive closure of the flipped relation is the
flipped closure: strong connectivity is closed under reversing every
arc. Private support for `isIrreducible_transpose`. -/
private theorem reflTransGen_flip {α : Type} {r : α → α → Prop} {i j : α}
    (hr : Relation.ReflTransGen r i j) :
    Relation.ReflTransGen (fun a b => r b a) j i := by
  induction hr with
  | refl => exact .refl
  | @tail b c _ hstep ih => exact Relation.ReflTransGen.head hstep ih

omit [Fintype V] [DecidableEq V] in
/-- Irreducibility is preserved by transposition: the support digraph
of `Mᵀ` is the arc-reversal of `M`'s, and strong connectivity is
invariant under reversing every arc. Unconditional hard crust; the
hypothesis form in which the transposed application is made. -/
theorem isIrreducible_transpose {M : Matrix V V ℝ} (h : M.IsIrreducible) :
    Mᵀ.IsIrreducible := by
  intro i j
  exact reflTransGen_flip (h j i)

/-- The walk transition matrix `P = D⁻¹ A` of a nonnegative irreducible
network with positive out-degrees is irreducible: row scaling by the
positive reciprocals `((deg a)⁻¹)` preserves the sign pattern, hence
the strongly-connected support digraph. Unconditional hard crust. -/
theorem walkTransitionMatrix_isIrreducible (A : WAdj (V := V))
    (hirr : A.IsIrreducible) (hdeg : ∀ i, 0 < deg A i) :
    (walkTransitionMatrix A).IsIrreducible := by
  intro i j
  refine reflTransGen_congr (fun a b hab => ?_) (hirr i j)
  rw [walkTransitionMatrix_apply]
  exact mul_pos (inv_pos.mpr (hdeg a)) hab

/-! ## Generic row-action helpers

Four small facts about the `vecMul` action absent from the pinned
Mathlib at these shapes, public because the Cesàro engine and the QA
both consume them directly. -/

omit [DecidableEq V] in
/-- Vector-matrix-matrix associativity in `vecMul` form — the
`ᵥ*`-shaped associate of `Matrix.mulVec_mulVec`, absent from the
pinned Mathlib. -/
theorem vecMul_mul (v : V → ℝ) (A B : Matrix V V ℝ) :
    (v ᵥ* A) ᵥ* B = v ᵥ* (A * B) := by
  rw [← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    ← Matrix.mulVec_transpose, Matrix.transpose_mul]

omit [DecidableEq V] in
/-- Entry form of the row action. -/
theorem vecMul_entry (v : V → ℝ) (M : Matrix V V ℝ) (j : V) :
    (v ᵥ* M) j = ∑ i, v i * M i j := by
  simp [Matrix.vecMul, Matrix.dotProduct, Matrix.transpose_apply]

omit [DecidableEq V] in
/-- Mass preservation under a row-stochastic action. -/
theorem sum_vecMul_eq_of_row_sum (M : Matrix V V ℝ) (hrow : ∀ i, ∑ j, M i j = 1)
    (v : V → ℝ) : ∑ j, (v ᵥ* M) j = ∑ j, v j := by
  simp only [vecMul_entry, Finset.sum_comm, ← Finset.mul_sum, hrow]
  simp

omit [DecidableEq V] in
/-- The row action commutes with finite sums of vectors. -/
theorem vecMul_sum (u : Finset ℕ) (g : ℕ → (V → ℝ)) (M : Matrix V V ℝ) :
    (∑ s in u, g s) ᵥ* M = ∑ s in u, (g s ᵥ* M) := by
  funext j
  simp only [vecMul_entry, Finset.sum_apply]
  calc ∑ x, (∑ c ∈ u, g c x) * M x j = ∑ x, ∑ c ∈ u, g c x * M x j :=
        Finset.sum_congr rfl fun x _ => Finset.sum_mul u (fun c => g c x) (M x j)
    _ = ∑ c ∈ u, ∑ x, g c x * M x j := Finset.sum_comm
    _ = ∑ c ∈ u, (g c ᵥ* M) j := Finset.sum_congr rfl fun c _ => (vecMul_entry _ _ _).symm

/-! ## Power entries of a nonnegative row-stochastic matrix -/

/-- Row sums of powers of a row-stochastic matrix stay one. -/
theorem pow_row_sum (M : Matrix V V ℝ) (hrow : ∀ i, ∑ j, M i j = 1) :
    ∀ (t : ℕ) (i : V), ∑ j, (M ^ t) i j = 1 := by
  intro t
  induction t with
  | zero => intro i; simp [Matrix.one_apply]
  | succ t ih =>
    intro i
    have hstep : ∑ j, (M ^ (t + 1)) i j = ∑ k, (M ^ t) i k * ∑ j, M k j := by
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ =>
        (Finset.mul_sum Finset.univ (fun x => M y x) ((M ^ t) i y)).symm
    rw [hstep]
    simp only [hrow, mul_one]
    exact ih i

/-- Entries of powers of a nonnegative matrix are nonnegative. -/
theorem pow_entry_nonneg (M : Matrix V V ℝ) (hnn : ∀ i j, 0 ≤ M i j) :
    ∀ (t : ℕ) (i j : V), 0 ≤ (M ^ t) i j := by
  intro t
  induction t with
  | zero =>
    intro i j
    rw [pow_zero M, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ t ih =>
    intro i j
    simp only [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hnn k j)

/-- Entries of powers of a nonnegative row-stochastic matrix stay in
`[0, 1]`. -/
theorem pow_entry_le_one (M : Matrix V V ℝ) (hnn : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j, M i j = 1) :
    ∀ (t : ℕ) (i j : V), (M ^ t) i j ≤ 1 := by
  have hbase : ∀ k j, M k j ≤ 1 := fun k j =>
    (Finset.single_le_sum (fun x _ => hnn k x) (Finset.mem_univ j)).trans_eq (hrow k)
  intro t
  induction t with
  | zero =>
    intro i j
    rw [pow_zero M, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ t ih =>
    intro i j
    simp only [pow_succ, Matrix.mul_apply]
    calc ∑ k, (M ^ t) i k * M k j ≤ ∑ k, (M ^ t) i k * 1 :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (hbase k j) (pow_entry_nonneg M hnn t i k)
      _ = 1 := by
          simp only [mul_one]
          exact pow_row_sum M hrow t i

/-! ## The Cesàro (Krylov–Bogoliubov) engine -/

/-- **Power positivity**: for a nonnegative irreducible matrix, every
index pair is joined by a power with a strictly positive entry — the
entry of a power dominates the product along any arc path. The
classical companion fact to `Matrix.IsIrreducible`, and the engine of
strict positivity below.

QA: exercised by `Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*`
(the return-arc pin at the second power and the existence form on the
asymmetric fixture). -/
theorem exists_pow_pos_of_isIrreducible {M : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ M i j)
    (hirr : M.IsIrreducible) (i j : V) : ∃ m : ℕ, 0 < (M ^ m) i j := by
  induction hirr i j with
  | refl => exact ⟨0, by simp [Matrix.one_apply]⟩
  | @tail b c _ hstep ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 1, ?_⟩
    have hpos : 0 < (M ^ m) i b * M b c := mul_pos hm hstep
    have hge : (M ^ m) i b * M b c ≤ ∑ k, (M ^ m) i k * M k c :=
      Finset.single_le_sum (fun k _ => mul_nonneg (pow_entry_nonneg M hnn m i k) (hnn k c))
        (Finset.mem_univ b)
    simp only [pow_succ, Matrix.mul_apply]
    exact lt_of_lt_of_le hpos hge

omit [DecidableEq V] in
/-- **Cluster points of averaged orbits are stationary** (the
Krylov–Bogoliubov lemma, finite form): for any matrix action and any
sequence `g` of nonnegative vectors of common nonnegative mass `m`
following the dynamics (`g s ᵥ* M = g (s+1)`), some cluster point of
the Cesàro means is a nonnegative stationary vector of the same mass.
No row-stochasticity is needed — mass preservation is carried by
`hgsum`. The proof: the means live in the compact simplex
`{x | 0 ≤ x ∧ ∑ x = m}` (Tychonoff + `IsCompact.tendsto_subseq`,
product topology), and their action-defect is the telescoping
remainder `t⁻¹ • (g 0 − g t)`, bounded entrywise by `2m/t → 0`.

QA: exercised through `exists_nonneg_stationary_of_row_stochastic` by
`Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*` (the
one-period-mean exact-stationarity pin and the orbit-oscillation fence
beside it). -/
theorem exists_cluster_stationary_of_orbit {M : Matrix V V ℝ}
    {m : ℝ} (hm : 0 ≤ m) {g : ℕ → (V → ℝ)}
    (hgnn : ∀ s i, 0 ≤ g s i) (hgsum : ∀ s, ∑ i, g s i = m)
    (hgstep : ∀ s, g s ᵥ* M = g (s + 1)) :
    ∃ σ : V → ℝ, (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i = m) ∧ σ ᵥ* M = σ := by
  -- the closed compact simplex
  have hSclosed : IsClosed {x : V → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = m} := by
    have hEq1 : {x : V → ℝ | ∀ i, x i ∈ Set.Ici (0 : ℝ)}
        = ⋂ i, {x : V → ℝ | x i ∈ Set.Ici (0 : ℝ)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    have h1 : IsClosed {x : V → ℝ | ∀ i, x i ∈ Set.Ici (0 : ℝ)} := by
      rw [hEq1]
      exact isClosed_iInter fun i => (isClosed_Ici (a := (0 : ℝ))).preimage (continuous_apply i)
    have h2 : IsClosed {x : V → ℝ | ∑ i, x i = m} :=
      isClosed_singleton.preimage
        (continuous_finset_sum Finset.univ fun i _ => continuous_apply i)
    have hEq : {x : V → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = m} =
        {x : V → ℝ | ∀ i, x i ∈ Set.Ici (0 : ℝ)} ∩ {x : V → ℝ | ∑ i, x i = m} := rfl
    rw [hEq]
    exact h1.inter h2
  have hSK : {x : V → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = m} ⊆
      Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) m) := fun x hx i _ =>
    ⟨hx.1 i, (Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ i)).trans_eq hx.2⟩
  have hScompact : IsCompact {x : V → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = m} :=
    (isCompact_univ_pi fun i => isCompact_Icc).of_isClosed_subset hSclosed hSK
  -- the Cesàro means of the orbit
  set μ : ℕ → (V → ℝ) :=
    fun t => ((t + 1 : ℕ) : ℝ)⁻¹ • ∑ s in Finset.range (t + 1), g s with hμdef
  have hμnn : ∀ (t : ℕ) (i : V), 0 ≤ μ t i := by
    intro t i
    have h1 : 0 ≤ ((t + 1 : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have h2 : 0 ≤ (∑ s in Finset.range (t + 1), g s) i := by
      rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun s _ => hgnn s i
    simp only [hμdef]
    exact mul_nonneg h1 h2
  have hμmass : ∀ t : ℕ, ∑ i, μ t i = m := by
    intro t
    simp only [hμdef, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm,
      Finset.sum_congr rfl fun s _ => hgsum s, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero t))]
  have hmem : ∀ t : ℕ, μ t ∈ {x : V → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = m} :=
    fun t => ⟨hμnn t, hμmass t⟩
  -- the telescoping defect identity
  have hμdefect : ∀ t : ℕ, μ t - μ t ᵥ* M = ((t + 1 : ℕ) : ℝ)⁻¹ • (g 0 - g (t + 1)) := by
    intro t
    have hstep' : ∑ s in Finset.range (t + 1), (g s ᵥ* M)
        = ∑ s in Finset.range (t + 1), g (s + 1) :=
      Finset.sum_congr rfl fun s _ => hgstep s
    have key : ∑ s in Finset.range (t + 1), g s - ∑ s in Finset.range (t + 1), g (s + 1)
        = g 0 - g (t + 1) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_range_sub' (fun s => g s) (t + 1)
    simp only [hμdef]
    rw [Matrix.vecMul_smul, vecMul_sum, hstep', ← smul_sub, key]
  have hdefbound : ∀ (t : ℕ) (j : V), |(μ t - μ t ᵥ* M) j| ≤ ((t + 1 : ℕ) : ℝ)⁻¹ * (2 * m) := by
    intro t j
    have hc : 0 ≤ ((t + 1 : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hg0 : (g 0) j ≤ m :=
      (Finset.single_le_sum (fun k _ => hgnn 0 k) (Finset.mem_univ j)).trans_eq (hgsum 0)
    have hgT : (g (t + 1)) j ≤ m :=
      (Finset.single_le_sum (fun k _ => hgnn (t + 1) k) (Finset.mem_univ j)).trans_eq
        (hgsum (t + 1))
    rw [hμdefect t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc, Pi.sub_apply]
    refine mul_le_mul_of_nonneg_left ?_ hc
    exact abs_le.2 ⟨by linarith [hgnn 0 j, hg0], by linarith [hgnn (t + 1) j, hgT]⟩
  -- extract a cluster point
  obtain ⟨π, hπmem, φ, hφmono, hcv⟩ := hScompact.tendsto_subseq hmem
  have hφle : ∀ k : ℕ, k ≤ φ k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hφmono (Nat.lt_succ_self k)))
  -- continuity of the action in the pi topology
  have hcont : ∀ j : V, Continuous fun x : V → ℝ => (x ᵥ* M) j := by
    intro j
    have hEq : (fun x : V → ℝ => (x ᵥ* M) j) = fun x => ∑ i, x i * M i j := by
      funext x
      exact vecMul_entry x M j
    rw [hEq]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  -- the shifted decay and the stationarity of the cluster point
  have hshift : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹) Filter.atTop (𝓝 0) := by
    have hmono : Monotone fun k : ℕ => ((k + 1 : ℕ) : ℝ) := fun a b hab =>
      Nat.cast_le.mpr (Nat.succ_le_succ hab)
    have hbdd : ∀ b : ℝ, ∃ a : ℕ, b ≤ ((a + 1 : ℕ) : ℝ) := by
      intro b
      obtain ⟨n, hn⟩ := exists_nat_gt b
      exact ⟨n, by rw [Nat.cast_succ]; linarith⟩
    exact tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_atTop_of_monotone hmono hbdd)
  have hdecay : Filter.Tendsto (fun k => ((k + 1 : ℕ) : ℝ)⁻¹ * (2 * m))
      Filter.atTop (𝓝 0) := by
    simpa using hshift.mul tendsto_const_nhds
  refine ⟨π, hπmem.1, hπmem.2, ?_⟩
  funext j
  have hzero : Filter.Tendsto (fun k => (μ (φ k) - μ (φ k) ᵥ* M) j) Filter.atTop (𝓝 0) := by
    refine (tendsto_zero_iff_abs_tendsto_zero
      (fun k => (μ (φ k) - μ (φ k) ᵥ* M) j)).mpr ?_
    refine squeeze_zero (fun k => abs_nonneg _) ?_ hdecay
    intro k
    have hle : ((φ k + 1 : ℕ) : ℝ)⁻¹ ≤ ((k + 1 : ℕ) : ℝ)⁻¹ := by
      rw [inv_le_inv₀ (Nat.cast_pos.mpr (Nat.succ_pos (φ k)))
        (Nat.cast_pos.mpr (Nat.succ_pos k)), Nat.cast_succ, Nat.cast_succ]
      exact add_le_add_right (Nat.cast_le.mpr (hφle k)) 1
    exact le_trans (hdefbound (φ k) j)
      (mul_le_mul_of_nonneg_right hle (by linarith : (0 : ℝ) ≤ 2 * m))
  have hcvj : Filter.Tendsto (fun k => μ (φ k) j) Filter.atTop (𝓝 (π j)) :=
    (tendsto_pi_nhds.mp hcv) j
  have hBj : Filter.Tendsto (fun k => (μ (φ k) ᵥ* M) j) Filter.atTop (𝓝 ((π ᵥ* M) j)) :=
    ((hcont j).tendsto π).comp hcv
  have hsub : Filter.Tendsto (fun k => μ (φ k) j - (μ (φ k) ᵥ* M) j) Filter.atTop
      (𝓝 (π j - (π ᵥ* M) j)) := hcvj.sub hBj
  have hfun : (fun k => μ (φ k) j - (μ (φ k) ᵥ* M) j)
      = fun k => (μ (φ k) - μ (φ k) ᵥ* M) j := by
    funext k
    simp only [Pi.sub_apply]
  rw [hfun] at hsub
  exact (sub_eq_zero.mp (tendsto_nhds_unique hsub hzero)).symm

/-- **Existence of a nonzero-mass nonnegative stationary vector for
any nonnegative row-stochastic matrix** — no irreducibility: the
Cesàro means of the orbit of `1` supply the stationary vector
(their mass is `|V|`). The honest scope statement — existence holds
on reducible chains too, exactly where uniqueness and positivity
provably fail (the reducibility fences in the QA).

QA: exercised by `Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*`
(the reducible-fixture instantiation). -/
theorem exists_nonneg_stationary_of_row_stochastic {M : Matrix V V ℝ}
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) [Nonempty V] :
    ∃ σ : V → ℝ, (∀ i, 0 ≤ σ i) ∧ (∑ i, σ i = Fintype.card V) ∧ σ ᵥ* M = σ := by
  obtain ⟨σ, hσnn, hσmass, hσstat⟩ := exists_cluster_stationary_of_orbit
    (m := (Fintype.card V : ℝ)) (Nat.cast_nonneg _) (g := fun t => (1 : V → ℝ) ᵥ* M ^ t)
    (fun s i => by
      simp only [vecMul_entry, Pi.one_apply, one_mul]
      exact Finset.sum_nonneg fun k _ => pow_entry_nonneg M hnn s k i)
    (fun s => by
      calc ∑ i, ((1 : V → ℝ) ᵥ* M ^ s) i = ∑ i, (1 : V → ℝ) i :=
          sum_vecMul_eq_of_row_sum (M ^ s) (pow_row_sum M hrow s) _
        _ = (Fintype.card V : ℝ) := by simp)
    (fun s => by
      show ((1 : V → ℝ) ᵥ* M ^ s) ᵥ* M = (1 : V → ℝ) ᵥ* M ^ (s + 1)
      rw [vecMul_mul, pow_succ])
  exact ⟨σ, hσnn, hσmass, hσstat⟩

/-! ## Strict positivity and min-ratio uniqueness under irreducibility

Two private matrix-level support lemmas; the public statements below
specialize them to the walk. -/

/-- Private: a nonzero nonnegative stationary vector of a nonnegative
irreducible action is strictly positive. -/
private theorem stationary_pos_aux {M : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ M i j)
    (hirr : M.IsIrreducible)
    {σ : V → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hσ0 : σ ≠ 0)
    (hσs : σ ᵥ* M = σ) : ∀ i, 0 < σ i := by
  have hiter : ∀ t : ℕ, σ ᵥ* M ^ t = σ := by
    intro t
    induction t with
    | zero =>
        simp only [pow_zero]
        exact Matrix.vecMul_one σ
    | succ t ih => rw [pow_succ, ← vecMul_mul, ih, hσs]
  intro i
  by_contra hcon
  rw [not_lt] at hcon
  have hzero : ∀ k, σ k = 0 := by
    intro k
    by_contra hpos'
    push_neg at hpos'
    have hkpos : 0 < σ k := lt_of_le_of_ne (hσ k) (Ne.symm hpos')
    obtain ⟨m, hm⟩ := exists_pow_pos_of_isIrreducible hnn hirr k i
    have heq : σ i = ∑ k', σ k' * (M ^ m) k' i := by
      have h0 := vecMul_entry σ (M ^ m) i
      rw [hiter m] at h0
      exact h0
    have hge : σ k * (M ^ m) k i ≤ ∑ k', σ k' * (M ^ m) k' i :=
      Finset.single_le_sum (fun k' _ => mul_nonneg (hσ k') (pow_entry_nonneg M hnn m k' i))
        (Finset.mem_univ k)
    have hlt : 0 < ∑ k', σ k' * (M ^ m) k' i := lt_of_lt_of_le (mul_pos hkpos hm) hge
    rw [← heq] at hlt
    linarith
  exact hσ0 (funext hzero)

/-- Private: two nonzero nonnegative stationary vectors of a
nonnegative irreducible action are positive multiples of each other
(the min-ratio trick). -/
private theorem stationary_smul_aux {M : Matrix V V ℝ} (hnn : ∀ i j, 0 ≤ M i j)
    (hirr : M.IsIrreducible)
    {σ τ : V → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hσ0 : σ ≠ 0) (hσs : σ ᵥ* M = σ)
    (hτ : ∀ i, 0 ≤ τ i) (hτ0 : τ ≠ 0) (hτs : τ ᵥ* M = τ) :
    ∃ c : ℝ, 0 < c ∧ σ = c • τ := by
  haveI : Nonempty V := (Function.ne_iff.mp hσ0).elim fun i _ => ⟨i⟩
  have hσpos := stationary_pos_aux hnn hirr hσ hσ0 hσs
  have hτpos := stationary_pos_aux hnn hirr hτ hτ0 hτs
  obtain ⟨j₀, -, hjmin⟩ :=
    Finset.exists_min_image Finset.univ (fun j => σ j / τ j) Finset.univ_nonempty
  have hc : ∀ j, σ j₀ / τ j₀ ≤ σ j / τ j := fun j => hjmin j (Finset.mem_univ j)
  have hnonneg : ∀ j, 0 ≤ σ j - (σ j₀ / τ j₀) * τ j := by
    intro j
    rw [sub_nonneg, ← le_div_iff₀ (hτpos j)]
    exact hc j
  have hdiff : (σ - (σ j₀ / τ j₀) • τ) ᵥ* M = σ - (σ j₀ / τ j₀) • τ := by
    rw [Matrix.sub_vecMul, Matrix.vecMul_smul, hσs, hτs]
  have hj₀ : σ j₀ - (σ j₀ / τ j₀) * τ j₀ = 0 := by
    have hcancel : σ j₀ / τ j₀ * τ j₀ = σ j₀ :=
      div_mul_cancel₀ (σ j₀) (ne_of_gt (hτpos j₀))
    linarith
  have hzero : σ - (σ j₀ / τ j₀) • τ = 0 := by
    by_contra hw
    have hpos := stationary_pos_aux hnn hirr hnonneg hw hdiff j₀
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hj₀] at hpos
    linarith
  refine ⟨σ j₀ / τ j₀, div_pos (hσpos j₀) (hτpos j₀), ?_⟩
  exact sub_eq_zero.mp hzero

/-! ## The walk-level stationary theory (hard crust) -/

/-- **The transposed Perron engine of the irreducible walk** (hard
crust since 2026-09-02, formerly conditional on `perron_frobenius`):
for a nonnegative irreducible network with a positive entry and
positive out-degrees, there is a strictly positive vector `v` fixed by
the transposed walk `Pᵀ *ᵥ v = v`, unique up to positive scalars among
the nonzero nonnegative fixed vectors. The proof: the Cesàro engine
produces a nonzero nonnegative stationary vector at the (irreducible)
walk, power positivity promotes it to strict positivity, and the
min-ratio trick gives the scale uniqueness — no Perron–Frobenius
machinery anywhere. The consumer-facing theorems below are all derived
from this engine.

QA: exercised by `Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*`
(the fixture instantiations and the reducibility fence). -/
theorem exists_walkPerronVector (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (hex : ∃ i j, 0 < A i j) (hdeg : ∀ i, 0 < deg A i) :
    ∃ v : V → ℝ, (∀ i, 0 < v i) ∧ (walkTransitionMatrix A)ᵀ *ᵥ v = v ∧
      ∀ y : V → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 →
        (walkTransitionMatrix A)ᵀ *ᵥ y = y → ∃ c : ℝ, 0 < c ∧ y = c • v := by
  haveI hV : Nonempty V := hex.elim fun i _ => ⟨i⟩
  have hPnn : ∀ i j, 0 ≤ walkTransitionMatrix A i j := fun i j => by
    rw [walkTransitionMatrix_apply]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt (hdeg i))) (hnn i j)
  have hProw : ∀ i, ∑ j, walkTransitionMatrix A i j = 1 := fun i =>
    walkTransitionMatrix_row_sum A hdeg i
  have hPirr : (walkTransitionMatrix A).IsIrreducible :=
    walkTransitionMatrix_isIrreducible A hirr hdeg
  obtain ⟨σ, hσnn, hσmass, hσstat⟩ := exists_nonneg_stationary_of_row_stochastic hPnn hProw
  have hσ0 : σ ≠ 0 := by
    intro h
    rw [h] at hσmass
    simp at hσmass
    have : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    linarith
  have hσpos := stationary_pos_aux hPnn hPirr hσnn hσ0 hσstat
  refine ⟨σ, hσpos, ?_, ?_⟩
  · rw [Matrix.mulVec_transpose]
    exact hσstat
  · intro y hy hy0 hyT
    have hys : y ᵥ* walkTransitionMatrix A = y := by
      rw [← Matrix.mulVec_transpose]
      exact hyT
    exact stationary_smul_aux hPnn hPirr hy hy0 hys hσnn hσ0 hσstat

/-- **Existence of a strictly positive stationary distribution** (hard
crust since 2026-09-02, formerly conditional on `perron_frobenius`).
Every nonnegative irreducible network with a positive entry and
positive out-degrees has a stationary distribution for its walk
`π ᵥ* P = π` that is strictly positive and normalized to total mass
`1`. This is the directed-axis statement the undirected shelf could
not reach: no symmetry hypothesis, no detailed balance, the vector
produced by the Cesàro engine rather than by the degree/volume formula
(the two agree on the symmetric cone; the QA witness pins the
agreement).

QA: exercised by `Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*`. -/
theorem exists_stationaryVec_of_irreducible (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (hex : ∃ i j, 0 < A i j) (hdeg : ∀ i, 0 < deg A i) :
    ∃ π : V → ℝ, (∀ i, 0 < π i) ∧ (∑ i, π i = 1) ∧
      π ᵥ* walkTransitionMatrix A = π := by
  haveI : Nonempty V := hex.elim fun i _ => ⟨i⟩
  obtain ⟨v, hv, hvT, -⟩ := exists_walkPerronVector A hnn hirr hex hdeg
  have hsumpos : 0 < ∑ i, v i := Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty
  refine ⟨(∑ i, v i)⁻¹ • v, fun i => mul_pos (inv_pos.mpr hsumpos) (hv i), ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hsumpos)
  · have hT : (walkTransitionMatrix A)ᵀ *ᵥ ((∑ i, v i)⁻¹ • v) = (∑ i, v i)⁻¹ • v := by
      rw [Matrix.mulVec_smul, hvT]
    exact (Matrix.mulVec_transpose _ _).symm.trans hT

/-- **Stationary vectors of an irreducible walk are unique up to
positive scale** (hard crust since 2026-09-02, formerly conditional on
`perron_frobenius`): any two nonzero nonnegative vectors fixed by the
walk `σ ᵥ* P = σ` are positive scalar multiples of each other. This is
the scale-free form of the uniqueness clause; the `∃!` packaging for
distributions is `existsUnique_stationaryVec_of_irreducible`.

QA: exercised — and its hypothesis-free form *refuted* on the reducible
two-block fixture — by
`Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*`. -/
theorem stationaryVec_smul_of_irreducible (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (hex : ∃ i j, 0 < A i j) (hdeg : ∀ i, 0 < deg A i)
    {σ τ : V → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hσ0 : σ ≠ 0)
    (hσs : σ ᵥ* walkTransitionMatrix A = σ)
    (hτ : ∀ i, 0 ≤ τ i) (hτ0 : τ ≠ 0)
    (hτs : τ ᵥ* walkTransitionMatrix A = τ) :
    ∃ c : ℝ, 0 < c ∧ τ = c • σ := by
  obtain ⟨v, -, -, huniq⟩ := exists_walkPerronVector A hnn hirr hex hdeg
  have hσT : (walkTransitionMatrix A)ᵀ *ᵥ σ = σ :=
    (Matrix.mulVec_transpose _ _).trans hσs
  have hτT : (walkTransitionMatrix A)ᵀ *ᵥ τ = τ :=
    (Matrix.mulVec_transpose _ _).trans hτs
  obtain ⟨c₁, hc₁, hσv⟩ := huniq σ hσ hσ0 hσT
  obtain ⟨c₂, hc₂, hτv⟩ := huniq τ hτ hτ0 hτT
  exact ⟨c₂ / c₁, div_pos hc₂ hc₁,
    by rw [hτv, hσv, smul_smul, div_mul_cancel₀ _ (ne_of_gt hc₁)]⟩

/-- **The stationary distribution of an irreducible walk exists and is
unique** (hard crust since 2026-09-02, formerly conditional on
`perron_frobenius`): there is exactly one nonnegative mass-one vector
fixed by the walk `π ᵥ* P = π`. This is the standard textbook statement
(e.g. Levin–Peres–Wilmer Theorem 1.7.2 for finite irreducible chains);
uniqueness is among *nonnegative* stationary distributions, with strict
positivity derived rather than hypothesized
(`stationaryVec_pos_of_irreducible`).

QA: exercised — and its hypothesis-free form *refuted* on the reducible
two-block fixture (two distinct stationary distributions exhibited with
nonnegativity, degrees, and row-stochasticity all verified) — by
`Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*`. -/
theorem existsUnique_stationaryVec_of_irreducible (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (hex : ∃ i j, 0 < A i j) (hdeg : ∀ i, 0 < deg A i) :
    ∃! π : V → ℝ, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧
      π ᵥ* walkTransitionMatrix A = π := by
  obtain ⟨π, hπpos, hπsum, hπs⟩ := exists_stationaryVec_of_irreducible A hnn hirr hex hdeg
  refine ⟨π, ⟨fun i => le_of_lt (hπpos i), hπsum, hπs⟩, ?_⟩
  intro τ ⟨hτnn, hτsum, hτs⟩
  have hπ0 : π ≠ 0 := by
    intro h; rw [h] at hπsum; simp at hπsum
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h] at hτsum; simp at hτsum
  obtain ⟨c, -, hc⟩ := stationaryVec_smul_of_irreducible A hnn hirr hex hdeg
    (fun i => le_of_lt (hπpos i)) hπ0 hπs hτnn hτ0 hτs
  have hc1 : c = 1 := by
    have h1 : ∑ i, τ i = c * ∑ i, π i := by
      rw [hc]; simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [hτsum, hπsum] at h1
    linarith
  rw [hc, hc1, one_smul]

/-- **Full support: no stationary vector of an irreducible walk can
vanish anywhere** (hard crust since 2026-09-02, formerly conditional
on `perron_frobenius`). Every nonzero nonnegative vector fixed by the
walk `σ ᵥ* P = σ` is strictly positive. The directed analogue of the
statement that on a connected undirected network the stationary
weights are all positive — here a consequence of power positivity
(strong connectivity eventually moves every mass everywhere),
available on genuinely asymmetric input where no degree/volume formula
reaches.

QA: exercised by `Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*`. -/
theorem stationaryVec_pos_of_irreducible (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (hex : ∃ i j, 0 < A i j) (hdeg : ∀ i, 0 < deg A i)
    {σ : V → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hσ0 : σ ≠ 0)
    (hσs : σ ᵥ* walkTransitionMatrix A = σ) : ∀ i, 0 < σ i := by
  obtain ⟨v, hv, -, huniq⟩ := exists_walkPerronVector A hnn hirr hex hdeg
  have hσT : (walkTransitionMatrix A)ᵀ *ᵥ σ = σ :=
    (Matrix.mulVec_transpose _ _).trans hσs
  obtain ⟨c, hc, hσv⟩ := huniq σ hσ hσ0 hσT
  intro i
  rw [hσv]
  exact mul_pos hc (hv i)

end SpectralGraphTheory
