/-
  SpectralCertificates.lean

  Purpose
  -------
  Step 3 of proposal `proposals/decidable-spectral-certificates.md`
  (High; Steps 0–2 delivered 2026-08-19): the computable certificate
  layer over the proved spectral center — proof-carrying upper bounds
  on the algebraic connectivity `lambda2`.

  The architecture this module implements: an *outside* numerical
  solver proposes an inexact test vector `v` and a candidate bound;
  Lean acts as the fully verified certificate validator. Checking is
  elementary arithmetic on the raw data (orthogonality to `onesVec`,
  positive norm, Dirichlet energy against the squared norm); soundness
  is a theorem — a checked certificate proves `lambda2 (A ℝ) ≤ bound`
  in the real spectral center. This closes, inside Lean, the
  noncomputable-extraction gap `docs/traction-plan.md` records as the
  reason broader engineering outreach stayed premature: nothing here
  needs the classical eigenvector machinery to *evaluate*.

  Two checkers are delivered, per the proposal's Step 0 Decision 2:

  - `isSpectralUpperBoundCertificate` — the ℚ-facing specification
    checker. Plain kernel `decide` cannot evaluate it (ℚ literals are
    opaque to kernel reduction — the recorded reducibility wall), so it
    is the *statement* layer: the soundness theorem
    `lambda2_le_of_certificate` is phrased against it, and it is
    reached through the proved bridges below, never by raw ℚ
    reduction.
  - `isSpectralUpperBoundCertificateInt` and its fractional-bound
    variant — the kernel-verifiable **integer cross-multiplied twin**:
    all certificate data in ℤ, the rational inequality replaced by
    `rawNumer ≤ 2 • bound • denom` (and, for a fractional bound
    `num/den` with `0 < den`, `den • rawNumer ≤ 2 • num • denom`).
    These kernel-`decide` on concrete `Fin n` graphs, giving the whole
    chain an executable, axiom-free entry point.

  Both checkers compare the *raw* Dirichlet sum
  `∑ i, ∑ j, A i j (v i − v j)²` against `2 • bound • ∑ i, (v i)²` —
  the cross-multiplied form of the proposal sketch's
  `(dir/2) ≤ bound • denom`, chosen so the ℚ and ℤ checkers have
  literally the same shape and the bridge between them is pure
  ordered-field algebra (cross-multiplication), no `decide`.

  Statement shapes (the proposal's "Sharp Edges" 1–2):

  - the ordered-field embedding is `algebraMap ℚ ℝ`, which is the
    rational coercion *definitionally* (`algebraMap_apply` is `rfl`);
    all transport lemmas go through the standard cast lemmas, so
    symmetry, quadratic forms, and Dirichlet sums transfer without
    re-elaborating any proof;
  - the zero-vector and orthogonality guards are conjuncts of both
    checkers, and the soundness theorem is QA-witnessed to be false
    without the orthogonality guard (the Rayleigh quotient of
    `onesVec` is `0` while `lambda2` is positive on connected graphs).

  The soundness proof is the proposal's flagship load-bearing consumer
  of the proved `lambda2_variational`: the certificate's raw Dirichlet
  sum is exactly `quadForm (laplacian A) v` (`laplacian_quadForm`), so
  `rawNumer/(2 • denom)` is the Rayleigh quotient of the embedded test
  vector, `dotOne = 0` places that vector in the constraint set
  `lambda2_variational` characterizes, and `lambda2 = sInf S ≤
  rayleigh v ≤ bound` falls out — an error in any link of that chain
  breaks this module rather than passing beside it. The reusable
  consumer form `lambda2_le_rayleigh` (division-form twin of
  `Expander.lambda2_mul_dotProduct_le_quadForm`) is exported for
  downstream test-vector arguments.

  Everything here is proved hard crust; this module adds no axioms.

  Related modules: the spectral center in
  `Scaffold.Mathlib.GraphTheory.Spectral`, the mixing lemma whose
  spectral hypothesis certified bounds feed in
  `Scaffold.Mathlib.GraphTheory.Expander`, and the QA witness chain in
  `Scaffold/QA/SpectralGraph/SpectralCertificates_QA.lean`.
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Group.Hom.Basic

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## 1. Transport of ℚ data into the real spectral center

The ordered-field embedding `algebraMap ℚ ℝ` is the rational coercion
definitionally, so every transport below is cast bookkeeping. These
lemmas are the proposal's Calibration 1 (faithful lifting of rational
computations without re-elaborating real proofs).
-/


/-- The ordered-field embedding agrees with the rational coercion:
`algebraMap ℚ ℝ q = (q : ℝ)` definitionally. This is the hinge every
transport lemma in this module goes through. -/
theorem algebraMap_apply (q : ℚ) : (algebraMap ℚ ℝ) q = (q : ℝ) := rfl

/-- A rational test vector embedded into the reals, entrywise. This is
the coercion the soundness theorem's witness runs on. -/
def toReal (v : V → ℚ) : V → ℝ := fun i => (v i : ℝ)

/-- An integer test vector embedded into the rationals, entrywise. -/
def toRat (v : V → ℤ) : V → ℚ := fun i => ((v i : ℤ) : ℚ)

omit [Fintype V] [DecidableEq V] in
/-- Symmetry transports along the ordered-field embedding. -/
theorem isSymm_map_algebraMap {A : Matrix V V ℚ} (hA : A.IsSymm) :
    (A.map (algebraMap ℚ ℝ)).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Matrix.map_apply]
  exact congrArg (algebraMap ℚ ℝ) (hA.apply i j)

omit [Fintype V] [DecidableEq V] in
/-- Symmetry transports along the integer embedding into ℚ. -/
theorem isSymm_map_intCast {A : Matrix V V ℤ} (hA : A.IsSymm) :
    (A.map (Int.cast : ℤ → ℚ)).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Matrix.map_apply]
  exact congrArg (Int.cast : ℤ → ℚ) (hA.apply i j)

omit [Fintype V] [DecidableEq V] in
/-- Symmetry transports along the integer embedding into ℝ. -/
theorem isSymm_map_intCastReal {A : Matrix V V ℤ} (hA : A.IsSymm) :
    (A.map (fun a => (a : ℝ))).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Matrix.map_apply]
  exact congrArg (fun a : ℤ => (a : ℝ)) (hA.apply i j)

omit [Fintype V] [DecidableEq V] in
/-- Nonnegativity transports along the ordered-field embedding. -/
theorem nonneg_map_algebraMap {A : Matrix V V ℚ}
    (hnn : ∀ i j, (0 : ℚ) ≤ A i j) (i j : V) :
    0 ≤ (A.map (algebraMap ℚ ℝ)) i j := by
  simp only [Matrix.map_apply]
  exact Rat.cast_nonneg.2 (hnn i j)

omit [DecidableEq V] in
/-- Dot products transport along the ordered-field embedding. -/
theorem dotProduct_toReal (v w : V → ℚ) :
    (toReal v) ⬝ᵥ (toReal w) = ((v ⬝ᵥ w : ℚ) : ℝ) := by
  simp only [toReal, Matrix.dotProduct, ← Rat.cast_mul, ← Rat.cast_sum]

omit [DecidableEq V] in
/-- The squared norm of an embedded rational test vector is the cast
of the checker's rational denominator. -/
theorem dotProduct_toReal_self (v : V → ℚ) :
    (toReal v) ⬝ᵥ (toReal v) = ((∑ i, (v i) ^ 2 : ℚ) : ℝ) := by
  rw [dotProduct_toReal]
  congr 1
  simp [Matrix.dotProduct, pow_two]

/-- The Dirichlet energy of an embedded rational test vector is the
cast of the raw rational Dirichlet sum: the certificate's `rawNumer`
is exactly the Laplacian quadratic form of the embedded vector, halved
(`laplacian_quadForm`). Load-bearing on the center's exact Laplacian
convention. -/
theorem quadForm_laplacian_map_algebraMap {A : Matrix V V ℚ}
    (hA : A.IsSymm) (v : V → ℚ) :
    quadForm (laplacian (A.map (algebraMap ℚ ℝ))) (toReal v)
      = ((∑ i, ∑ j, A i j * (v i - v j) ^ 2 : ℚ) : ℝ) / 2 := by
  rw [laplacian_quadForm _ (isSymm_map_algebraMap hA) (toReal v)]
  have hterm : ∀ i j : V,
      (A.map (algebraMap ℚ ℝ)) i j * (toReal v i - toReal v j) ^ 2
        = ((A i j * (v i - v j) ^ 2 : ℚ) : ℝ) := by
    intro i j
    simp only [Matrix.map_apply, toReal]
    rw [algebraMap_apply (A i j)]
    push_cast
    ring
  have houter : ∑ i, ∑ j, ((A i j * (v i - v j) ^ 2 : ℚ) : ℝ)
      = ((∑ i, ∑ j, A i j * (v i - v j) ^ 2 : ℚ) : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => (Rat.cast_sum Finset.univ
      (fun j => A i j * (v i - v j) ^ 2)).symm), ← Rat.cast_sum]
  exact congrArg (· / 2)
    ((Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => hterm i j).trans houter)

omit [Fintype V] [DecidableEq V] in
/-- The real matrix of an integer network: casting twice (ℤ → ℚ → ℝ)
is casting once. -/
theorem map_intCast_real (A : Matrix V V ℤ) :
    (A.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ ℝ)
      = A.map (fun a => (a : ℝ)) := by
  refine Matrix.ext fun i j => ?_
  simp [Matrix.map_apply, Rat.cast_intCast]

/-!
## 2. The one-sided Rayleigh consumer form

The division-form consumer twin of
`Expander.lambda2_mul_dotProduct_le_quadForm`: every admissible test
vector bounds `lambda2` from above. Proved straight from the
characterization `lambda2_variational` — the constraint-set membership
plus PSD boundedness — so any consumer of this lemma is load-bearing
on that proved characterization.
-/


/-- **One-sided Rayleigh bound (consumer form).** On a symmetric
nonnegative network, every nonzero test vector orthogonal to
`onesVec` certifies `lambda2 ≤ R_L(x)`. This is the division-form
twin of `Expander.lambda2_mul_dotProduct_le_quadForm`, proved straight
from `lambda2_variational` (`lambda2` is the infimum over exactly
these test vectors; the constraint set is bounded below by `0` through
`laplacian_psd`). The certificate soundness theorem below is the
flagship consumer of this route. -/
theorem lambda2_le_rayleigh (A : WAdj (V := V)) (hsymm : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V)
    {x : V → ℝ} (hx0 : x ≠ 0)
    (hxorth : Matrix.dotProduct x onesVec = 0) :
    lambda2 A hsymm hcard ≤ rayleigh (laplacian A) x := by
  rw [lambda2_variational A hsymm hnn hcard]
  refine csInf_le ?_ ⟨x, hx0, hxorth, rfl⟩
  refine ⟨0, fun r hr => ?_⟩
  obtain ⟨y, hy0, -, hyr⟩ := hr
  rw [← hyr, rayleigh, if_neg hy0]
  exact div_nonneg (laplacian_psd A hsymm hnn y) (dotProduct_self_pos hy0).le

/-!
## 3. The rational certificate and its soundness
-/


/-- The ℚ-facing upper-bound certificate checker (specification
layer). Checks, entirely in rational arithmetic, that the test vector
`v` is orthogonal to the all-ones vector, is nonzero, and has
Dirichlet energy `rawNumer` bounded by `2 • bound • denom` — the
cross-multiplied form of `rawNumer / (2 • denom) ≤ bound`, i.e. of the
Rayleigh quotient bound `R_L(v) ≤ bound`.

Kernel `decide` cannot evaluate this checker (the Step 0 reducibility
wall: ℚ literals are opaque to kernel reduction); consume it through
the proved twin bridges `isSpectralUpperBoundCertificateInt_iff` /
`isSpectralUpperBoundCertificateIntFrac_iff` or the soundness theorem
`lambda2_le_of_certificate`.

QA: exercised end-to-end (through the bridge, by kernel `decide` on
the integer twin) in
`Scaffold/QA/SpectralGraph/SpectralCertificates_QA.lean`. -/
def isSpectralUpperBoundCertificate (A : Matrix V V ℚ) (v : V → ℚ)
    (bound : ℚ) : Bool :=
  let dotOne := ∑ i, v i
  let denom := ∑ i, (v i) ^ 2
  let rawNumer := ∑ i, ∑ j, A i j * (v i - v j) ^ 2
  (dotOne == 0) && decide (0 < denom) && decide (rawNumer ≤ 2 * bound * denom)

/-! The `let`-shaped checker definitions do not produce usable simp
equation lemmas, so each checker gets a public `rfl` unfolding lemma
(zeta-reduction plus `== 0` normalization to `decide`). -/
omit [DecidableEq V] in
/-- Unfolding lemma for the rational checker. -/
theorem isSpectralUpperBoundCertificate_eq (A : Matrix V V ℚ) (v : V → ℚ)
    (bound : ℚ) :
    isSpectralUpperBoundCertificate A v bound
      = (decide (∑ i, v i = 0) && decide (0 < ∑ i, (v i) ^ 2)
        && decide (∑ i, ∑ j, A i j * (v i - v j) ^ 2
          ≤ 2 * bound * ∑ i, (v i) ^ 2)) := rfl

/-- **Certificate soundness (ℚ-facing).** If the rational checker
accepts `(A, v, bound)` on a symmetric nonnegative rational network
with at least two vertices, then the embedded real network's algebraic
connectivity satisfies `lambda2 ≤ bound`.

The proof is the proposal's checked-by-hand route, now machine-checked:
`rawNumer/2` is `quadForm (laplacian A ℝ) (toReal v)` and `denom` its
squared norm (`laplacian_quadForm` + transport), `dotOne = 0` is
orthogonality to `onesVec`, so `toReal v` is an admissible test vector
and `lambda2_le_rayleigh` — the `lambda2_variational` consumer —
bounds `lambda2` by the quotient, which the cross-multiplied
hypothesis pins below `bound`. Load-bearing on `lambda2_variational`,
`laplacian_quadForm`, and the ordered-field transport: an error in any
breaks soundness rather than passing beside it.

QA: instantiated on the four-cycle in
`Scaffold/QA/SpectralGraph/SpectralCertificates_QA.lean` (accepted
certificate ⇒ `lambda2 ≤ 2`), with the orthogonality guard refuted
on omission there. -/
theorem lambda2_le_of_certificate {A : Matrix V V ℚ} (hsymm : A.IsSymm)
    (hnn : ∀ i j, (0 : ℚ) ≤ A i j) (hcard : 2 ≤ Fintype.card V)
    (v : V → ℚ) (bound : ℚ)
    (hcert : isSpectralUpperBoundCertificate A v bound = true) :
    lambda2 (A.map (algebraMap ℚ ℝ)) (isSymm_map_algebraMap hsymm) hcard
      ≤ ((bound : ℚ) : ℝ) := by
  rw [isSpectralUpperBoundCertificate_eq] at hcert
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hcert
  obtain ⟨⟨hdot, hden⟩, hdir⟩ := hcert
  -- the embedded test vector and its admissibility
  have hxorth : Matrix.dotProduct (toReal v) onesVec = 0 := by
    have hone : onesVec = toReal (fun _ : V => (1 : ℚ)) := by
      funext i; simp [onesVec, toReal]
    rw [hone, dotProduct_toReal]
    have hsum : v ⬝ᵥ (fun _ : V => (1 : ℚ)) = ∑ i, v i := by
      simp [Matrix.dotProduct]
    rw [hsum]
    exact_mod_cast hdot
  have hxden : 0 < ((∑ i, (v i) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hden
  have hx0 : toReal v ≠ 0 := by
    intro hcon
    have hnorm := dotProduct_toReal_self v
    rw [hcon, Matrix.zero_dotProduct] at hnorm
    rw [← hnorm] at hxden
    exact lt_irrefl 0 hxden
  -- the quotient bound: rayleigh = rawNumer / (2 • denom) ≤ bound
  refine le_trans (lambda2_le_rayleigh (A.map (algebraMap ℚ ℝ))
    (isSymm_map_algebraMap hsymm)
    (fun i j => nonneg_map_algebraMap hnn i j) hcard hx0 hxorth) ?_
  rw [rayleigh, if_neg hx0, quadForm_laplacian_map_algebraMap hsymm v,
    dotProduct_toReal_self]
  -- ((rawNumer : ℝ) / 2) / ((denom : ℝ)) ≤ (bound : ℝ)
  have hcast : ((∑ i, ∑ j, A i j * (v i - v j) ^ 2 : ℚ) : ℝ)
      ≤ 2 * ((bound : ℚ) : ℝ) * ((∑ i, (v i) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast hdir
  rw [div_le_iff₀ (by exact hxden : (0 : ℝ) < ((∑ i, (v i) ^ 2 : ℚ) : ℝ)),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linear_combination hcast

/-!
## 4. The kernel-verifiable integer twin

All certificate data in ℤ; the rational inequality cross-multiplied.
These checkers kernel-`decide` on concrete vertex types (the Step 0
spike verified `C₄`/`C₆` acceptance and rejection paths).
-/


/-- The kernel-verifiable **integer cross-multiplied twin** of the
rational checker: adjacency entries, test vector, and bound all
integer; the certificate inequality is `rawNumer ≤ 2 • bound • denom`
with `denom > 0` — the cross-multiplied form of
`rawNumer / (2 • denom) ≤ bound`, so `bound` is an *integer* upper
bound on `lambda2`. Kernel `decide` evaluates this on concrete `Fin n`
graphs (accept and reject paths — see the QA module).

QA: accept/reject/non-orthogonal/zero-vector paths kernel-decided on
the four-cycle in
`Scaffold/QA/SpectralGraph/SpectralCertificates_QA.lean`. -/
def isSpectralUpperBoundCertificateInt (A : Matrix V V ℤ) (v : V → ℤ)
    (bound : ℤ) : Bool :=
  let dotOne := ∑ i, v i
  let denom := ∑ i, (v i) ^ 2
  let rawNumer := ∑ i, ∑ j, A i j * (v i - v j) ^ 2
  (dotOne == 0) && decide (0 < denom) && decide (rawNumer ≤ 2 * bound * denom)

omit [DecidableEq V] in
/-- Unfolding lemma for the integer twin, same rationale as
`isSpectralUpperBoundCertificate_eq`. -/
theorem isSpectralUpperBoundCertificateInt_eq (A : Matrix V V ℤ) (v : V → ℤ)
    (bound : ℤ) :
    isSpectralUpperBoundCertificateInt A v bound
      = (decide (∑ i, v i = 0) && decide (0 < ∑ i, (v i) ^ 2)
        && decide (∑ i, ∑ j, A i j * (v i - v j) ^ 2
          ≤ 2 * bound * ∑ i, (v i) ^ 2)) := rfl

/-- The fractional-bound twin: the certificate bound is the rational
`num / den` with `0 < den`, and the cross-multiplied inequality is
`den • rawNumer ≤ 2 • num • denom`. This is the shape a solver
emitting non-integer bounds (e.g. `5/2`) lands in, and the form the
proved cross-multiplication bridge
`isSpectralUpperBoundCertificateIntFrac_iff` connects to the ℚ-facing
checker.

QA: accept (`5/2`) and reject (`3/2`) paths kernel-decided on the
four-cycle in
`Scaffold/QA/SpectralGraph/SpectralCertificates_QA.lean`. -/
def isSpectralUpperBoundCertificateIntFrac (A : Matrix V V ℤ) (v : V → ℤ)
    (num den : ℤ) : Bool :=
  let dotOne := ∑ i, v i
  let denom := ∑ i, (v i) ^ 2
  let rawNumer := ∑ i, ∑ j, A i j * (v i - v j) ^ 2
  (dotOne == 0) && decide (0 < denom) && decide (0 < den)
    && decide (den * rawNumer ≤ 2 * num * denom)

omit [DecidableEq V] in
/-- Unfolding lemma for the fractional twin, same rationale as
`isSpectralUpperBoundCertificate_eq`. -/
theorem isSpectralUpperBoundCertificateIntFrac_eq (A : Matrix V V ℤ)
    (v : V → ℤ) (num den : ℤ) :
    isSpectralUpperBoundCertificateIntFrac A v num den
      = (decide (∑ i, v i = 0) && decide (0 < ∑ i, (v i) ^ 2)
        && decide (0 < den) && decide (den * ∑ i, ∑ j, A i j * (v i - v j) ^ 2
          ≤ 2 * num * ∑ i, (v i) ^ 2)) := rfl

omit [DecidableEq V] in
/-- The integer-twin checker on ℤ data decides exactly the rational
checker on the cast data with the same integer bound: the twin is
*sound and complete* against the specification, at the price of only
ordered-field algebra (no `decide` in the proof). -/
theorem isSpectralUpperBoundCertificateInt_iff (A : Matrix V V ℤ)
    (v : V → ℤ) (bound : ℤ) :
    isSpectralUpperBoundCertificateInt A v bound = true ↔
      isSpectralUpperBoundCertificate (A.map (Int.cast : ℤ → ℚ))
        (toRat v) bound = true := by
  rw [isSpectralUpperBoundCertificateInt_eq,
    isSpectralUpperBoundCertificate_eq]
  simp only [Bool.and_eq_true, decide_eq_true_iff, toRat, Matrix.map_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
      by exact_mod_cast h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
      by exact_mod_cast h3⟩

omit [DecidableEq V] in
/-- **The proved cross-multiplication bridge (fractional form).** With
a positive denominator, the fractional integer twin accepts
`(A, v, num, den)` exactly when the rational specification checker
accepts the cast data at the rational bound `num / den`. The
mathematical content is cross-multiplication in an ordered field —
`rawNumer ≤ 2 • (num/den) • denom` with `0 < den` and `0 < denom` iff
`den • rawNumer ≤ 2 • num • denom` — plus integer-cast transport of
the finite sums. Pure algebra, no `decide`; this is the lemma that
makes the ℚ-facing specification *reachable* from kernel-verifiable
integer arithmetic. The `0 < den` hypothesis is genuinely needed for
the reverse direction (the ℚ-side bound `num / den` alone cannot see
the sign of `den`). -/
theorem isSpectralUpperBoundCertificateIntFrac_iff (A : Matrix V V ℤ)
    (v : V → ℤ) (num den : ℤ) (hden : (0 : ℤ) < den) :
    isSpectralUpperBoundCertificateIntFrac A v num den = true ↔
      isSpectralUpperBoundCertificate (A.map (Int.cast : ℤ → ℚ))
        (toRat v) (((num : ℤ) : ℚ) / ((den : ℤ) : ℚ)) = true := by
  rw [isSpectralUpperBoundCertificateIntFrac_eq,
    isSpectralUpperBoundCertificate_eq]
  simp only [Bool.and_eq_true, decide_eq_true_iff, toRat, Matrix.map_apply]
  have hd : (0 : ℚ) < ((den : ℤ) : ℚ) := by exact_mod_cast hden
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3⟩
    refine ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, ?_⟩
    -- cross-multiply: dir ≤ 2 • (num/den) • denom ↔ den • dir ≤ 2 • num • denom
    have h3cast : (((den : ℤ) * ∑ i, ∑ j, A i j * (v i - v j) ^ 2 : ℤ) : ℚ)
        ≤ (((2 * num * ∑ i, (v i) ^ 2 : ℤ) : ℤ) : ℚ) := by exact_mod_cast h3
    push_cast at h3cast
    rw [← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ hd]
    linear_combination h3cast
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, hden⟩, ?_⟩
    -- reverse cross-multiplication
    rw [← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ hd] at h3
    rw [mul_comm]
    exact_mod_cast h3

/-!
## 5. Kernel-facing soundness corollaries

Composing the twin bridges with the ℚ-facing soundness theorem: a
kernel-`decide`d integer certificate yields a verified bound on
`lambda2` of the real network. The transfer below goes through a
`subst`-based equality transfer because `lambda2`'s symmetry argument
is a proof term (rewriting the matrix directly would leave it
stale); proof irrelevance then absorbs the difference.
-/


/-- `lambda2` respects propositional equality of the underlying
matrix (the symmetry hypothesis transfers, and proof irrelevance
absorbs the difference between symmetry proofs). -/
theorem lambda2_le_of_matrix_eq {M N : Matrix V V ℝ} (hM : M.IsSymm)
    (hN : N.IsSymm) (hEq : M = N) (hcard : 2 ≤ Fintype.card V)
    (hle : lambda2 M hM hcard ≤ r) : lambda2 N hN hcard ≤ r := by
  subst hEq
  exact hle

/-- **Certificate soundness (kernel-verifiable twin).** If the integer
cross-multiplied checker accepts `(A, v, bound)` on a symmetric
nonnegative integer network with at least two vertices, then the real
network's algebraic connectivity satisfies `lambda2 ≤ bound`. The
hypothesis is kernel-`decide`able on concrete vertex types, so this is
the executable end-to-end chain: integer arithmetic → `decide` →
proved bridge → real spectral bound.

QA: instantiated on the four-cycle (certified `lambda2 ≤ 2`) in
`Scaffold/QA/SpectralGraph/SpectralCertificates_QA.lean`. -/
theorem lambda2_le_of_certificateInt {A : Matrix V V ℤ} (hsymm : A.IsSymm)
    (hnn : ∀ i j, (0 : ℤ) ≤ A i j) (hcard : 2 ≤ Fintype.card V)
    (v : V → ℤ) (bound : ℤ)
    (h : isSpectralUpperBoundCertificateInt A v bound = true) :
    lambda2 (A.map (fun a => (a : ℝ))) (isSymm_map_intCastReal hsymm) hcard
      ≤ ((bound : ℤ) : ℝ) := by
  refine lambda2_le_of_matrix_eq (isSymm_map_algebraMap
    (isSymm_map_intCast hsymm)) (isSymm_map_intCastReal hsymm)
    (map_intCast_real A) hcard ?_
  refine le_trans (lambda2_le_of_certificate (isSymm_map_intCast hsymm)
    (fun i j => Int.cast_nonneg.2 (hnn i j)) hcard (toRat v) bound
    ((isSpectralUpperBoundCertificateInt_iff A v bound).mp h)) ?_
  push_cast
  exact le_rfl

/-- **Certificate soundness (fractional twin).** If the fractional
integer checker accepts `(A, v, num, den)` with `0 < den` on a
symmetric nonnegative integer network, then the real network's
algebraic connectivity satisfies `lambda2 ≤ num / den`.

QA: instantiated on the four-cycle (certified `lambda2 ≤ 5/2`) in
`Scaffold/QA/SpectralGraph/SpectralCertificates_QA.lean`. -/
theorem lambda2_le_of_certificateIntFrac {A : Matrix V V ℤ}
    (hsymm : A.IsSymm) (hnn : ∀ i j, (0 : ℤ) ≤ A i j)
    (hcard : 2 ≤ Fintype.card V) (v : V → ℤ) (num den : ℤ)
    (hden : (0 : ℤ) < den)
    (h : isSpectralUpperBoundCertificateIntFrac A v num den = true) :
    lambda2 (A.map (fun a => (a : ℝ))) (isSymm_map_intCastReal hsymm) hcard
      ≤ (((((num : ℤ) : ℚ) / ((den : ℤ) : ℚ)) : ℚ) : ℝ) := by
  refine lambda2_le_of_matrix_eq (isSymm_map_algebraMap
    (isSymm_map_intCast hsymm)) (isSymm_map_intCastReal hsymm)
    (map_intCast_real A) hcard ?_
  exact lambda2_le_of_certificate (isSymm_map_intCast hsymm)
    (fun i j => Int.cast_nonneg.2 (hnn i j)) hcard (toRat v)
    (((num : ℤ) : ℚ) / ((den : ℤ) : ℚ))
    ((isSpectralUpperBoundCertificateIntFrac_iff A v num den hden).mp h)

end SpectralGraphTheory
