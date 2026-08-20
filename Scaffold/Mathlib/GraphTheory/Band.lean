/-
  Band.lean

  Purpose
  -------
  Two-sided spectral band projectors: the orthogonal projector onto the
  span of the eigenvectors whose eigenvalues lie in a spectral interval
  `(a, b]`, defined as the difference of two `spectralProjector` calls —
  `bandProjector M hM a b = spectralProjector M hM b - spectralProjector M hM a`
  — together with its basic properties and the orthogonality of disjoint
  bands (Steps 1 and 2 of `proposals/spectral-band-projectors.md`, the
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

  Open steps of the proposal (not in this module): Step 3, completeness
  over a partition of the spectrum; Step 4, the Hilbert-projection
  specialization.

  Related modules: the below-threshold projector and its algebra live in
  `Scaffold.Mathlib.GraphTheory.Spectral`; the Tikhonov filter
  (`GraphTheory.Tikhonov`) is the attenuating (non-projector) counterpart
  of this exact-selection family.
-/

import Scaffold.Mathlib.GraphTheory.Spectral

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

end SpectralGraphTheory
