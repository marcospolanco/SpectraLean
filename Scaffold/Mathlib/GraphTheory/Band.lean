/-
  Band.lean

  Purpose
  -------
  Two-sided spectral band projectors: the orthogonal projector onto the
  span of the eigenvectors whose eigenvalues lie in a spectral interval
  `(a, b]`, defined as the difference of two `spectralProjector` calls —
  `bandProjector M hM a b = spectralProjector M hM b - spectralProjector M hM a`
  — together with its basic properties, the orthogonality of disjoint
  bands, and completeness under a partition of the spectrum (Steps 1, 2,
  and 3 of `proposals/spectral-band-projectors.md`, the
  Active priority table's High row at delivery time). Pure hard crust: no
  `axiom` declarations;
  every theorem is proved from the already-proved algebra of
  `Scaffold.Mathlib.GraphTheory.Spectral` — symmetry
  (`spectralProjector_symmetric`), the nestedness product law
  (`spectralProjector_mul_spectralProjector` and its ordered forms, added
  alongside this module), the extreme-threshold theorems
  (`spectralProjector_eq_zero`, `spectralProjector_eq_one`), and the
  eigenvector-action lemmas (`spectralProjector_mulVec_eigvecOf_self`,
  `spectralProjector_mulVec_eigvecOf_of_lt`).

  Design (per the proposal's design note): the band is parameterized by
  a spectral *interval* `(a, b]`, not by an eigenvalue index. The
  definition is total — when `a > b` it evaluates to the negation of the
  `(b, a]` band and none of the projector properties are claimed for it;
  every property below carries `a ≤ b` exactly where it is needed. The
  below-spectrum special case is the named corollary
  `bandProjector_eq_spectralProjector_of_lt` (`spectralProjector`
  itself is kept, not re-derived), and a covering band recovers the
  identity (`bandProjector_eq_one`).

  The mode-selection interface is the pair of action lemmas: every
  eigenvector with eigenvalue strictly between `a` and `b` is fixed
  (`bandProjector_mulVec_eigvecOf_self`), and every eigenvector outside
  the band is annihilated (`...eq_zero_left`, `...eq_zero_right`) — the
  bandpass-filtering behavior named by the proposal's external consumer
  (frequency-selective analysis in graph signal processing; context,
  not citation).

  Step 2 of the proposal is delivered here as well: orthogonality of
  disjoint bands. When `(a, b]` and `(c, d]` are disjoint (`b ≤ c`, each
  band nonnegated), the two band projectors compose to zero in both
  orders (`bandProjector_mul_bandProjector_eq_zero`, `...'`), their
  images are orthogonal in the dot-product sense
  (`bandProjector_inner_eq_zero`), and no nonzero vector is fixed by
  both (`eq_zero_of_bandProjector_mulVec_eq_self` — the subspace-level
  reading of the proposal's "they share no eigenvector").

  Step 3 is delivered here too: completeness under a partition. The
  algebraic engine is an unconditional telescoping law — the sum of the
  consecutive band projectors of *any* threshold sequence `t` collapses
  to the difference of the two extreme below-threshold projectors
  (`sum_range_bandProjector_eq_sub`); when the sequence covers the
  spectrum (start strictly below every eigenvalue, end at or above
  them all), that difference is the identity
  (`sum_range_bandProjector_eq_one`), and dually every signal is the
  sum of its band components (`sum_range_bandProjector_mulVec_eq_self`)
  — the resolution of the identity the proposal's external consumer
  consumes. Monotonicity of the family is deliberately *not* a
  hypothesis of the sum identity (telescoping does not use it); it is
  exactly what the fourth theorem consumes — distinct members of a
  monotone family compose to zero (`..._eq_zero_of_monotone`), which is
  what makes the family a partition rather than a mere sequence.

  Open step of the proposal: none — Step 4 (the Hilbert-projection
  specialization) is delivered below, completing the program. The band
  projector's action is Mathlib's orthogonal projection onto its range
  (`bandProjector_toEuclidean_apply_eq_orthogonalProjection`), and it is
  the closest point of that range to the input
  (`norm_sub_bandProjector_apply_le`) — the Hilbert projection theorem
  instantiated at the band's range through the `toEuclideanLin`
  transport, the resolvent Step-0 record's precedent.

  Related modules: the below-threshold projector and its algebra live in
  `Scaffold.Mathlib.GraphTheory.Spectral`; the Tikhonov filter
  (`GraphTheory.Tikhonov`) is the attenuating (non-projector) counterpart
  of this exact-selection family.
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The two-sided spectral band projector: the difference of the
below-threshold projectors at `b` and at `a`, projecting onto the span
of every eigenvector whose eigenvalue lies in `(a, b]`.

For `a ≤ b` this is an orthogonal projector
(`bandProjector_idempotent`, `bandProjector_symmetric`) that fixes each
in-band eigenvector and annihilates each out-of-band one. The
definition is total: when `a > b` it is the negation of the `(b, a]`
band, a deliberate junk value documented here rather than guarded in
the type. -/
noncomputable def bandProjector (M : Matrix V V ℝ) (hM : M.IsSymm)
    (a b : ℝ) : Matrix V V ℝ :=
  spectralProjector M hM b - spectralProjector M hM a

/-- Band projectors are symmetric: the difference of two symmetric
matrices. -/
theorem bandProjector_symmetric (M : Matrix V V ℝ) (hM : M.IsSymm)
    (a b : ℝ) :
    (bandProjector M hM a b).IsSymm :=
  (spectralProjector_symmetric M hM b).sub
    (spectralProjector_symmetric M hM a)

/-- Band projectors are idempotent when the interval is nonempty
(`a ≤ b`): nestedness of the threshold projectors makes the difference
of two idempotents idempotent — `(P_b − P_a)² = P_b − P_a` because
`P_a P_b = P_b P_a = P_a`. This is where the proposal's "transfers
cheaply from the existing idempotence argument" cashes out: it needs
the cross-threshold product law, not just idempotence of each factor
(differences of idempotents are not idempotent in general). -/
theorem bandProjector_idempotent (M : Matrix V V ℝ) (hM : M.IsSymm)
    (a b : ℝ) (hab : a ≤ b) :
    bandProjector M hM a b * bandProjector M hM a b
      = bandProjector M hM a b := by
  rw [bandProjector, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul,
    spectralProjector_idempotent M hM b,
    spectralProjector_mul_spectralProjector_of_le' M hM hab,
    spectralProjector_mul_spectralProjector_of_le M hM hab,
    spectralProjector_idempotent M hM a, sub_self, sub_zero]

/-- In-band modes are fixed: an eigenvector whose eigenvalue is
strictly above `a` and at most `b` is fixed by the band projector — the
bandpass-selection interface for graph signal processing. -/
theorem bandProjector_mulVec_eigvecOf_self (M : Matrix V V ℝ)
    (hM : M.IsSymm) (a b : ℝ) (i : V)
    (h₁ : a < eigvalOf M hM i) (h₂ : eigvalOf M hM i ≤ b) :
    bandProjector M hM a b *ᵥ eigvecOf M hM i = eigvecOf M hM i := by
  rw [bandProjector, Matrix.sub_mulVec,
    spectralProjector_mulVec_eigvecOf_self M hM b i h₂,
    spectralProjector_mulVec_eigvecOf_of_lt M hM a i h₁, sub_zero]

/-- Below-band modes are annihilated: an eigenvector with eigenvalue at
most `a` lies in the subtracted threshold projector, so the band
projector kills it. -/
theorem bandProjector_mulVec_eigvecOf_eq_zero_left (M : Matrix V V ℝ)
    (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b) (i : V)
    (h : eigvalOf M hM i ≤ a) :
    bandProjector M hM a b *ᵥ eigvecOf M hM i = 0 := by
  rw [bandProjector, Matrix.sub_mulVec,
    spectralProjector_mulVec_eigvecOf_self M hM b i (h.trans hab),
    spectralProjector_mulVec_eigvecOf_self M hM a i h, sub_self]

/-- Above-band modes are annihilated: an eigenvector with eigenvalue
strictly above `b` lies outside both threshold projectors. -/
theorem bandProjector_mulVec_eigvecOf_eq_zero_right (M : Matrix V V ℝ)
    (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b) (i : V)
    (h : b < eigvalOf M hM i) :
    bandProjector M hM a b *ᵥ eigvecOf M hM i = 0 := by
  rw [bandProjector, Matrix.sub_mulVec,
    spectralProjector_mulVec_eigvecOf_of_lt M hM b i h,
    spectralProjector_mulVec_eigvecOf_of_lt M hM a i (hab.trans_lt h),
    sub_zero]

/-- Below the whole spectrum, the band projector *is* the
below-threshold projector: the named special case of the proposal's
design note — `spectralProjector` is kept as the one-sided projector
and recovered here rather than re-derived. -/
theorem bandProjector_eq_spectralProjector_of_lt (M : Matrix V V ℝ)
    (hM : M.IsSymm) (a b : ℝ) (h : ∀ i, a < eigvalOf M hM i) :
    bandProjector M hM a b = spectralProjector M hM b := by
  rw [bandProjector, spectralProjector_eq_zero M hM a h, sub_zero]

/-- A covering band is the identity: with `a` strictly below the whole
spectrum and `b` above it, every mode is in-band. The two-band instance
of the completeness statement Step 3 of the proposal generalizes to
partitions. -/
theorem bandProjector_eq_one (M : Matrix V V ℝ) (hM : M.IsSymm)
    (a b : ℝ) (ha : ∀ i, a < eigvalOf M hM i)
    (hb : ∀ i, eigvalOf M hM i ≤ b) :
    bandProjector M hM a b = 1 := by
  rw [bandProjector_eq_spectralProjector_of_lt M hM a b ha,
    spectralProjector_eq_one M hM b hb]

/-! ### Step 2: orthogonality of disjoint bands

The pairwise half of the completeness statement Step 3 generalizes to
partitions: two bands over disjoint spectral intervals project onto
orthogonal subspaces. All three statements below are load-bearing on the
Step-1 nestedness cross-law — the product of two band projectors expands
through its ordered forms to `P_{min b d} − P_{min b c} − P_{min a d} +
P_{min a c}`, which collapses under the ordering hypotheses. -/

/-- Disjoint bands compose to zero, forward order: when `(a, b]` and
`(c, d]` are disjoint (`b ≤ c`, with each band nonnegated so `a ≤ b` and
`c ≤ d`), the product `B_{a,b} * B_{c,d}` vanishes. The `b ≤ c`
hypothesis is exactly interval disjointness and is load-bearing:
overlapping bands sharing an eigenvalue compose to a nonzero matrix (the
QA overlap guard refutes the hypothesis-free form). -/
theorem bandProjector_mul_bandProjector_eq_zero (M : Matrix V V ℝ)
    (hM : M.IsSymm) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hbc : b ≤ c) :
    bandProjector M hM a b * bandProjector M hM c d = 0 := by
  rw [bandProjector, bandProjector, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.sub_mul,
    spectralProjector_mul_spectralProjector_of_le M hM (hbc.trans hcd),
    spectralProjector_mul_spectralProjector_of_le M hM
      (hab.trans (hbc.trans hcd)),
    spectralProjector_mul_spectralProjector_of_le M hM hbc,
    spectralProjector_mul_spectralProjector_of_le M hM (hab.trans hbc),
    sub_self]

/-- Disjoint bands compose to zero, flipped order: `B_{c,d} * B_{a,b} = 0`
as well, by the same four-term expansion through the flipped nestedness
forms. Together with the forward order this says the two band images are
mutually annihilating subspaces. -/
theorem bandProjector_mul_bandProjector_eq_zero' (M : Matrix V V ℝ)
    (hM : M.IsSymm) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hbc : b ≤ c) :
    bandProjector M hM c d * bandProjector M hM a b = 0 := by
  rw [bandProjector, bandProjector, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.sub_mul,
    spectralProjector_mul_spectralProjector_of_le' M hM (hbc.trans hcd),
    spectralProjector_mul_spectralProjector_of_le' M hM hbc,
    spectralProjector_mul_spectralProjector_of_le' M hM
      (hab.trans (hbc.trans hcd)),
    spectralProjector_mul_spectralProjector_of_le' M hM (hab.trans hbc),
    sub_self, sub_self, sub_zero]

/-- The images of disjoint bands are orthogonal: for any two vectors,
the low-band image of one is dot-orthogonal to the high-band image of
the other. This is the frequency-selective consumer's form of
orthogonality — filtered components from disjoint bands carry no shared
signal — and follows from the composition law by moving the first band
across the dot product (its transpose is itself). -/
theorem bandProjector_inner_eq_zero (M : Matrix V V ℝ) (hM : M.IsSymm)
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (hbc : b ≤ c)
    (x y : V → ℝ) :
    (bandProjector M hM a b *ᵥ x) ⬝ᵥ (bandProjector M hM c d *ᵥ y)
      = 0 := by
  have hB₁ : bandProjector M hM a b *ᵥ x
      = x ᵥ* (bandProjector M hM a b)ᵀ :=
    (Matrix.vecMul_transpose _ _).symm
  rw [hB₁, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    show (bandProjector M hM a b)ᵀ = bandProjector M hM a b from
      bandProjector_symmetric M hM a b,
    bandProjector_mul_bandProjector_eq_zero M hM a b c d hab hcd hbc,
    Matrix.vecMul_zero, Matrix.zero_dotProduct]

/-- Disjoint bands share no mode: a vector fixed by both band
projectors is zero — the subspace-level reading of the proposal's "they
share no eigenvector". A common fixed vector would be simultaneously a
low-band and a high-band signal, which the disjointness of the intervals
forbids. -/
theorem eq_zero_of_bandProjector_mulVec_eq_self (M : Matrix V V ℝ)
    (hM : M.IsSymm) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hbc : b ≤ c) (w : V → ℝ)
    (h₁ : bandProjector M hM a b *ᵥ w = w)
    (h₂ : bandProjector M hM c d *ᵥ w = w) :
    w = 0 := by
  have key : bandProjector M hM c d *ᵥ (bandProjector M hM a b *ᵥ w)
      = 0 := by
    rw [Matrix.mulVec_mulVec,
      bandProjector_mul_bandProjector_eq_zero' M hM a b c d hab hcd hbc,
      Matrix.zero_mulVec]
  rw [h₁, h₂] at key
  exact key

/-! ### Step 3: completeness under a partition

The assembling statement of the proposal's design note: a family of
disjoint bands covering the spectral range resolves the identity. The
engine is the *unconditional* telescoping law below — the sum of
consecutive band projectors collapses to the difference of the extreme
below-threshold projectors for **any** threshold sequence, ordered or
not (the junk bands of a non-monotone family cancel in pairs). The
completeness theorem adds exactly the two endpoint covering hypotheses
that turn that difference into `1 − 0`; monotonicity, which the sum
identity does not consume, is the hypothesis of the orthogonality
theorem, where it is what makes the family a partition. -/

/-- The telescoping law: the sum of the consecutive band projectors of
any threshold sequence `t` — ordered or not — collapses to the
difference of the below-threshold projectors at the sequence's ends.
This is the algebraic engine of completeness, and it is load-bearing on
the band definition's exact difference shape: a sign-flipped or
transposed definition would leave an uncancellable residue. -/
theorem sum_range_bandProjector_eq_sub (M : Matrix V V ℝ) (hM : M.IsSymm)
    (t : ℕ → ℝ) (n : ℕ) :
    ∑ k in Finset.range n, bandProjector M hM (t k) (t (k + 1))
      = spectralProjector M hM (t n) - spectralProjector M hM (t 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, bandProjector]
      abel

/-- **Completeness under a partition.** For a threshold family whose
first term is strictly below every eigenvalue and whose `n`-th term is
at or above them all, the sum of the consecutive band projectors is the
identity — every mode of the spectrum lies in exactly one band of the
induced partition. Both covering hypotheses are load-bearing: a family
starting above the lowest mode drops it (the sum is missing that mode's
projector), and a family ending below the highest mode drops that one
(the QA endpoint guards refute the hypothesis-free form in both
directions). Monotonicity is deliberately not a hypothesis here — the
telescoping law consumes only the endpoints — and is delivered as the
orthogonality theorem below, where it is exactly what is used. -/
theorem sum_range_bandProjector_eq_one (M : Matrix V V ℝ) (hM : M.IsSymm)
    (t : ℕ → ℝ) (n : ℕ)
    (hb : ∀ i, t 0 < eigvalOf M hM i)
    (hc : ∀ i, eigvalOf M hM i ≤ t n) :
    ∑ k in Finset.range n, bandProjector M hM (t k) (t (k + 1)) = 1 := by
  rw [sum_range_bandProjector_eq_sub M hM t n,
    spectralProjector_eq_one M hM (t n) hc,
    spectralProjector_eq_zero M hM (t 0) hb, sub_zero]

/-- Distinct members of a monotone threshold family are orthogonal: for
`k < m`, the bands `(t k, t (k+1)]` and `(t m, t (m+1)]` are disjoint,
so their projectors compose to zero. Monotonicity is load-bearing here
— it supplies exactly the interval disjointness `t (k+1) ≤ t m` that
Step 2's composition law consumes — and this is what makes the family
a partition: together with completeness, the identity resolves into
mutually orthogonal band projectors. -/
theorem bandProjector_mul_bandProjector_eq_zero_of_monotone
    (M : Matrix V V ℝ) (hM : M.IsSymm) (t : ℕ → ℝ) (ht : Monotone t)
    (k m : ℕ) (hkm : k < m) :
    bandProjector M hM (t k) (t (k + 1)) * bandProjector M hM (t m) (t (m + 1))
      = 0 :=
  bandProjector_mul_bandProjector_eq_zero M hM (t k) (t (k + 1))
    (t m) (t (m + 1)) (ht (Nat.le_succ k)) (ht (Nat.le_succ m))
    (ht (show k + 1 ≤ m by omega))

/-- The consumer's form of completeness: under the same covering
hypotheses, every vector is the sum of its band components — the
frequency-band decomposition a graph-signal-processing consumer
filters with. The matrix-to-vector pass is the `mulVec` analog of
Mathlib's `Matrix.sum_mul` (not present in the pinned snapshot in this
shape), proved by interchanging the two finite sums. -/
theorem sum_range_bandProjector_mulVec_eq_self (M : Matrix V V ℝ)
    (hM : M.IsSymm) (t : ℕ → ℝ) (n : ℕ)
    (hb : ∀ i, t 0 < eigvalOf M hM i)
    (hc : ∀ i, eigvalOf M hM i ≤ t n) (x : V → ℝ) :
    ∑ k in Finset.range n, bandProjector M hM (t k) (t (k + 1)) *ᵥ x = x := by
  have hsplit : ∑ k in Finset.range n,
      bandProjector M hM (t k) (t (k + 1)) *ᵥ x
      = (∑ k in Finset.range n, bandProjector M hM (t k) (t (k + 1))) *ᵥ x := by
    funext i
    simp only [Matrix.mulVec, Matrix.dotProduct, Finset.sum_apply,
      Matrix.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hsplit, sum_range_bandProjector_eq_one M hM t n hb hc,
    Matrix.one_mulVec]

/-! ### Step 4: the Hilbert-projection specialization

The closing statement of the proposal: the band projector's output is
the closest point of its own range to the input. Mathlib's Hilbert
projection theorem is instantiated at `K := LinearMap.range
(toEuclideanLin B)` through the Euclidean transport (the resolvent
Step-0 record's precedent); the engine is the residual-orthogonality
fact below, which consumes exactly the two Step-1 facts — symmetry
(moving the band across the dot product) and idempotence (collapsing
`B *ᵥ (x − B *ᵥ x)` to `0`).

Statements are made at `EuclideanSpace ℝ V`, the honest Hilbert-space
norm. The bare type `V → ℝ` carries the sup-norm instance by default,
which is deliberately not used for any closest-point claim. -/

/-- The residual of the band projector is orthogonal to its range, in
dot-product form: for any signal `x` and any range member `B *ᵥ z`, the
out-of-band residual carries no in-band signal. Load-bearing on both
Step-1 facts: symmetry moves the band across the dot product, and
idempotence collapses the band of the residual to zero. -/
theorem bandProjector_residual_dotProduct_eq_zero
    (M : Matrix V V ℝ) (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b)
    (x z : V → ℝ) :
    (x - bandProjector M hM a b *ᵥ x) ⬝ᵥ
      (bandProjector M hM a b *ᵥ z) = 0 := by
  have hmove : (x - bandProjector M hM a b *ᵥ x) ᵥ*
      bandProjector M hM a b
      = bandProjector M hM a b *ᵥ
          (x - bandProjector M hM a b *ᵥ x) := by
    conv_rhs => rw [← Matrix.vecMul_transpose]
    rw [show (bandProjector M hM a b)ᵀ = bandProjector M hM a b from
      bandProjector_symmetric M hM a b]
  rw [Matrix.dotProduct_mulVec, hmove, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, bandProjector_idempotent M hM a b hab,
    sub_self, Matrix.zero_dotProduct]

/-- Transport of the band action: under the Euclidean packaging, the
band projector maps the packaged signal to the packaged filtered
signal. (`WithLp` is a type synonym on this Mathlib snapshot, so the
packaging is definitionally the identity; the lemma fixes the
*syntactic* form consumers rewrite with.) -/
private theorem toEuclideanLin_bandProjector_apply
    (M : Matrix V V ℝ) (hM : M.IsSymm) (a b : ℝ) (x : V → ℝ) :
    Matrix.toEuclideanLin (bandProjector M hM a b)
        ((WithLp.equiv 2 (V → ℝ)).symm x)
      = (WithLp.equiv 2 (V → ℝ)).symm
          (bandProjector M hM a b *ᵥ x) := by
  rw [Matrix.toEuclideanLin_piLp_equiv_symm, Matrix.toLin'_apply]

/-- **Step 4: the Hilbert-projection identification.** Under the
Euclidean transport, Mathlib's orthogonal projection of a signal onto
the band's range is exactly the band-filtered signal — the band
projector *is* the closest-point map of its own range, instantiated
through `eq_orthogonalProjection_of_mem_of_inner_eq_zero` (membership of
the filtered signal via the transport above; orthogonality of the
residual via `bandProjector_residual_dotProduct_eq_zero`). -/

theorem bandProjector_toEuclidean_apply_eq_orthogonalProjection
    (M : Matrix V V ℝ) (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b)
    (x : V → ℝ) :
    (orthogonalProjection
        (LinearMap.range
          (Matrix.toEuclideanLin (bandProjector M hM a b)))
        ((WithLp.equiv 2 (V → ℝ)).symm x) : EuclideanSpace ℝ V)
      = (WithLp.equiv 2 (V → ℝ)).symm
          (bandProjector M hM a b *ᵥ x) := by
  refine eq_orthogonalProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [LinearMap.mem_range]
    exact ⟨(WithLp.equiv 2 (V → ℝ)).symm x,
      toEuclideanLin_bandProjector_apply M hM a b x⟩
  · intro w hw
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hw
    have hz' : w = (WithLp.equiv 2 (V → ℝ)).symm
        (bandProjector M hM a b *ᵥ
          ((WithLp.equiv 2 (V → ℝ)) z)) :=
      hz ▸ (toEuclideanLin_bandProjector_apply M hM a b _).symm
    rw [hz']
    have hdiff : (WithLp.equiv 2 (V → ℝ)).symm x -
        (WithLp.equiv 2 (V → ℝ)).symm (bandProjector M hM a b *ᵥ x)
        = (WithLp.equiv 2 (V → ℝ)).symm
            (x - bandProjector M hM a b *ᵥ x) := rfl
    rw [hdiff, EuclideanSpace.inner_piLp_equiv_symm]
    simpa using bandProjector_residual_dotProduct_eq_zero M hM a b
      hab x ((WithLp.equiv 2 (V → ℝ)) z)

/-- **Step 4: the closest-point property.** For every fixed point `y`
of the band projector — equivalently, by idempotence, every member of
its range — the filtered signal `B *ᵥ x` is at least as close to `x` as
`y` is: the band projector's output is the closest point in its range
to the input, the Hilbert projection theorem's conclusion instantiated
at the band. Derived from `orthogonalProjection_minimal` composed with
the identification above; the fixed-point hypothesis is load-bearing
(the QA guard exhibits a non-range competitor strictly closer than the
projection, refuting the hypothesis-free form). -/
theorem norm_sub_bandProjector_apply_le
    (M : Matrix V V ℝ) (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b)
    (x y : V → ℝ) (hy : bandProjector M hM a b *ᵥ y = y) :
    ‖(WithLp.equiv 2 (V → ℝ)).symm x -
      (WithLp.equiv 2 (V → ℝ)).symm (bandProjector M hM a b *ᵥ x)‖
      ≤ ‖(WithLp.equiv 2 (V → ℝ)).symm x -
        (WithLp.equiv 2 (V → ℝ)).symm y‖ := by
  have hmin := orthogonalProjection_minimal
    (U := LinearMap.range
      (Matrix.toEuclideanLin (bandProjector M hM a b)))
    ((WithLp.equiv 2 (V → ℝ)).symm x)
  rw [bandProjector_toEuclidean_apply_eq_orthogonalProjection
    M hM a b hab x] at hmin
  have hmem : (WithLp.equiv 2 (V → ℝ)).symm y ∈ LinearMap.range
      (Matrix.toEuclideanLin (bandProjector M hM a b)) := by
    rw [LinearMap.mem_range]
    refine ⟨(WithLp.equiv 2 (V → ℝ)).symm y, ?_⟩
    rw [toEuclideanLin_bandProjector_apply M hM a b y, hy]
  have hbdd : BddBelow (Set.range fun
      c : LinearMap.range
        (Matrix.toEuclideanLin (bandProjector M hM a b)) =>
      ‖(WithLp.equiv 2 (V → ℝ)).symm x - (c : EuclideanSpace ℝ V)‖) :=
    ⟨0, fun r hr => by
      obtain ⟨c, rfl⟩ := hr
      exact norm_nonneg _⟩
  exact hmin.le.trans
    (ciInf_le hbdd ⟨(WithLp.equiv 2 (V → ℝ)).symm y, hmem⟩)

end SpectralGraphTheory
