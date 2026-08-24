import Scaffold.Mathlib.LinearAlgebra.PerronFrobenius
import Scaffold.Mathlib.GraphTheory.Normalized

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
distribution is instead a Perron–Frobenius statement: it is the
positive left eigenvector of the walk at its Perron root, which for a
row-stochastic matrix is `1`.

**Trust boundary.** The four stationary-distribution theorems below are
*conditional on the `perron_frobenius` axiom* — Lean-checked deductions
whose conclusions inherit that axiom's trust cost; they are not
foundationally proved. The two irreducibility-transfer lemmas
(`isIrreducible_transpose`, `walkTransitionMatrix_isIrreducible`) are
unconditional hard crust. The engine makes two axiom applications and
consumes the axiom's clause 5 (any nonnegative eigenvector's eigenvalue
is the Perron root — pinning the walk's Perron root to `1` through the
shelf's row-stochasticity `walkTransitionMatrix_mulVec_one` at
`onesVec`) and clause 6 (uniqueness up to positive scalars — both the
scale-uniqueness of stationary vectors and the `∃!` packaging); the
transposed application's root is pinned by the bilinear pairing
`v ⬝ᵥ (P *ᵥ u) = (Pᵀ *ᵥ v) ⬝ᵥ u` (the pin's `Matrix.dotProduct_mulVec`
and `Matrix.mulVec_transpose`) against the already-pinned first
application. No characteristic polynomial, rootMultiplicity, or
complex-domination clause is used.

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
  primitivity, which the axiom deliberately does not claim (the
  `strict_dominance_refuted_QA` imprimitivity fence).

## Support lemmas

Two small `Relation.ReflTransGen` congruence facts absent from the
pinned Mathlib are private: a relation congruence (the pin has `mono`
for `ReflGen` only) and the flipped-closure transfer behind
`isIrreducible_transpose`.

Delivered 2026-08-24 (`proposals/irreducible-stationary-distributions.md`).
-/

open scoped Matrix

namespace SpectralGraphTheory

open Matrix

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
hypothesis form in which the transposed Perron–Frobenius application is
made. -/
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

/-- **The transposed Perron engine of the irreducible walk**
(conditional on `perron_frobenius`). For a nonnegative irreducible
network with a positive entry and positive out-degrees, there is a
strictly positive vector `v` fixed by the transposed walk
`Pᵀ *ᵥ v = v`, unique up to positive scalars among the nonzero
nonnegative fixed vectors. This is the Perron vector of `Pᵀ` at its
Perron root, with the root *computed to be `1`*: the first axiom
application pins the root of `P` itself to `1` through the
eigenvalue-identification clause at `onesVec` (row stochasticity), and
the bilinear pairing `v ⬝ᵥ (P *ᵥ u) = (Pᵀ *ᵥ v) ⬝ᵥ u` transfers the
pin to the transposed application through the positivity of
`v ⬝ᵥ u`. The consumer-facing theorems below are all derived from this
engine.

QA: exercised by `Scaffold.QA.SpectralGraph.IrreducibleStationary_QA.*`
(the fixture instantiations and the reducibility fence). -/
theorem exists_walkPerronVector (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (hirr : A.IsIrreducible)
    (hex : ∃ i j, 0 < A i j) (hdeg : ∀ i, 0 < deg A i) :
    ∃ v : V → ℝ, (∀ i, 0 < v i) ∧ (walkTransitionMatrix A)ᵀ *ᵥ v = v ∧
      ∀ y : V → ℝ, (∀ i, 0 ≤ y i) → y ≠ 0 →
        (walkTransitionMatrix A)ᵀ *ᵥ y = y → ∃ c : ℝ, 0 < c ∧ y = c • v := by
  haveI hV : Nonempty V := hex.elim fun i _ => ⟨i⟩
  set P := walkTransitionMatrix A with hPdef
  have hPnn : ∀ i j, 0 ≤ P i j := fun i j => by
    rw [hPdef, walkTransitionMatrix_apply]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt (hdeg i))) (hnn i j)
  have hPirr : P.IsIrreducible := walkTransitionMatrix_isIrreducible A hirr hdeg
  obtain ⟨i₀, j₀, hex₀⟩ := hex
  have hP₀ : 0 < P i₀ j₀ := by
    rw [hPdef, walkTransitionMatrix_apply]
    exact mul_pos (inv_pos.mpr (hdeg i₀)) hex₀
  have hPex : ∃ i j, 0 < P i j := ⟨i₀, j₀, hP₀⟩
  obtain ⟨r, u, hr, hu, hPu, -, hval, -, -⟩ :=
    Scaffold.LinearAlgebra.perron_frobenius P hPnn hPirr hPex
  have hr1 : r = 1 := by
    refine (hval 1 (1 : V → ℝ) (fun _ => zero_le_one) (fun h => ?_) ?_).symm
    · exact one_ne_zero (congrFun h hV.some)
    · exact (walkTransitionMatrix_mulVec_one A hdeg).trans (one_smul ℝ _).symm
  have hPTnn : ∀ i j, 0 ≤ Pᵀ i j := fun i j => hPnn j i
  have hPTirr : Pᵀ.IsIrreducible := isIrreducible_transpose hPirr
  have hPTex : ∃ i j, 0 < Pᵀ i j := ⟨j₀, i₀, by
    simpa [Matrix.transpose_apply] using hP₀⟩
  obtain ⟨s, v, hs, hv, hPvT, -, -, huniqT, -⟩ :=
    Scaffold.LinearAlgebra.perron_frobenius Pᵀ hPTnn hPTirr hPTex
  have hs1 : s = 1 := by
    have hkey : v ⬝ᵥ (P *ᵥ u) = (Pᵀ *ᵥ v) ⬝ᵥ u := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have hlhs : v ⬝ᵥ (P *ᵥ u) = v ⬝ᵥ u := by rw [hPu, hr1, one_smul]
    have hvpos : 0 < v ⬝ᵥ u :=
      Finset.sum_pos (fun i _ => mul_pos (hv i) (hu i)) Finset.univ_nonempty
    have h2 : v ⬝ᵥ (P *ᵥ u) = s * (v ⬝ᵥ u) := by
      rw [hkey, hPvT, smul_dotProduct, smul_eq_mul]
    have hcomb : v ⬝ᵥ u = s * (v ⬝ᵥ u) := hlhs.symm.trans h2
    exact (mul_right_cancel₀ (ne_of_gt hvpos) (by rw [one_mul]; exact hcomb)).symm
  refine ⟨v, hv, ?_, ?_⟩
  · rw [hPvT, hs1, one_smul]
  · intro y hy hy0 hyT
    exact huniqT 1 y hy hy0 (by rw [hyT, one_smul])

/-- **Existence of a strictly positive stationary distribution**
(conditional on `perron_frobenius`). Every nonnegative irreducible
network with a positive entry and positive out-degrees has a stationary
distribution for its walk `π ᵥ* P = π` that is strictly positive and
normalized to total mass `1`. This is the directed-axis statement the
undirected shelf could not reach: no symmetry hypothesis, no detailed
balance, the vector produced by Perron–Frobenius rather than by the
degree/volume formula (the two agree on the symmetric cone; the QA
witness pins the agreement).

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
positive scale** (conditional on `perron_frobenius`): any two nonzero
nonnegative vectors fixed by the walk `σ ᵥ* P = σ` are positive scalar
multiples of each other. This is the scale-free form of the uniqueness
clause; the `∃!` packaging for distributions is
`existsUnique_stationaryVec_of_irreducible`.

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
unique** (conditional on `perron_frobenius`): there is exactly one
nonnegative mass-one vector fixed by the walk `π ᵥ* P = π`. This is the
standard textbook statement (e.g. Levin–Peres–Wilmer Theorem 1.7.2 for
finite irreducible chains); uniqueness is among *nonnegative*
stationary distributions, with strict positivity derived rather than
hypothesized (`stationaryVec_pos_of_irreducible`).

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
vanish anywhere** (conditional on `perron_frobenius`). Every nonzero
nonnegative vector fixed by the walk `σ ᵥ* P = σ` is strictly positive.
The directed analogue of the statement that on a connected undirected
network the stationary weights are all positive — here a consequence of
the Perron vector's strict positivity through the uniqueness clause,
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
