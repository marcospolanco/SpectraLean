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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!
# Relative entropy and Shannon entropy for finite distributions

`proposals/finite-relative-entropy.md`, delivered: the two classical
information-theoretic quantities for distributions on a `Fintype`, with
the two textbook facts that make them usable — Gibbs' inequality
(`klDiv_nonneg`, `klDiv_eq_zero_iff`) and the entropy maximum
(`shannonEntropy_le_log_card`,
`shannonEntropy_eq_log_card_iff`). This closes the entropy half of
`docs/6_SGT_BACKLOG.md` item 6 (the reversibility half is
`GraphTheory.Stationary`'s detailed-balance layer).

**Everything here is proved hard crust: zero axioms.** The route is the
term-wise information inequality (Cover & Thomas, *Elements of
Information Theory*, Theorem 2.6.3 — their own proof routes through
`log t ≤ t − 1` term-wise): each KL summand dominates `a − b` by
`Real.one_sub_inv_le_log_of_pos`, with equality forcing `a = b` through
`Real.log_lt_sub_one_of_pos`. The proposal's surveyed Jensen route
(`StrictConcaveOn.map_sum_eq_iff'` applied to
`strictConcaveOn_log_Ioi`) is also fully present in the pinned Mathlib
and yields the same statements; the term-wise route was chosen because
it needs no Finset-`smul` plumbing, no `Ioi`-membership side
conditions, and no support-finset filtering.

**Junk-value discipline** (the electrical-resistance precedent): a
summand with `a = 0` contributes exactly `0`, written as an explicit
`if a = 0 then 0 else …` in the definition rather than left implicit.
Every theorem's hypotheses (`0 ≤ p i`, `∑ p = 1`, `0 < q i`, `∑ q = 1`)
are exactly what rules the junk cases in; the QA file exhibits the
convention visibly at the delta distribution.

Downstream consumers this serves: the mixing-time program's
`chiSquareDistance` is the quadratic member of the same family of
distribution-distances, and relative entropy against the stationary
measure is the classical refinement of the same ℓ²(π) geometry;
`docs/3_SPECTRAL_THEORY.md`'s retained x90 pipeline names a "spectral
entropy H(t)" that `shannonEntropy` now gives a real definition to
(spectral entropy itself stays deferred per the proposal).

**The entropy leg of the mixing program** (2026-09-01,
`proposals/entropy-mixing-pinsker.md`): the entropy–χ² bridge
`klDiv_le_sum_sq_div`, the two-block log-sum bound
`sum_klTerm_ge_klTerm` (the first internal consumption of Gibbs'
inequality — the rescaling proof composes `sub_le_klTerm` on the
block), and the binary two-point Pinsker bound
`klTerm_add_klTerm_one_sub_ge_two_sq` (`2(a−b)² ≤ d(a‖b)`, proved by
an explicit FTC identity — `d(a‖b) = ∫_b^a (a−t)/(t(1−t)) dt ≥
∫_b^a 4(a−t) dt` through the AM-GM step `t(1−t) ≤ 1/4`; a genuinely
second-order fact that the first-order log bounds cannot close).
These are `GraphTheory.Mixing`'s Pinsker conversion and entropy-decay
theorems' engines — `InformationTheory.Entropy`'s first graph-level
consumers, recorded from birth as this module's intended downstream.

QA: `Scaffold/QA/InformationTheory/Entropy_QA.lean` (the scalar pins)
and `Scaffold/QA/SpectralGraph/Mixing_QA.lean` (the graph instances).
-/

open scoped Classical BigOperators

namespace Scaffold.InformationTheory

variable {V : Type*} [Fintype V]

/-! ### The definitions -/

/-- One Kullback–Leibler summand: `a * log (a / b)` for `a ≠ 0`, and
exactly `0` when `a = 0` (the visible junk convention — the term is
`0` regardless of `b`, so a zero-probability index never contributes).
The whole edifice below is built from this scalar term. -/
noncomputable def klTerm (a b : ℝ) : ℝ :=
  if a = 0 then 0 else a * Real.log (a / b)

/-- Kullback–Leibler divergence (relative entropy) of `p` from `q`:
`klDiv p q = ∑ i, p i * log (p i / q i)`, zero-`p`-terms omitted.
Meaningful under `0 ≤ p`, `∑ p = 1`, `0 < q`, `∑ q = 1`, where it is
nonnegative and vanishes exactly at `p = q` (Gibbs' inequality
below). `q i = 0` is junk (division by zero) and is excluded by the
strict positivity hypothesis every theorem carries. -/
noncomputable def klDiv (p q : V → ℝ) : ℝ :=
  ∑ i, klTerm (p i) (q i)

/-- Shannon entropy of `p`: `shannonEntropy p = -∑ i, p i * log (p i)`,
zero-`p`-terms omitted, so each negated summand is nonnegative and the
sign of the quantity is visible in the definition. Meaningful under
`0 ≤ p`, `∑ p = 1`, where it is nonnegative and at most
`log (Fintype.card V)`, with equality exactly at the uniform
distribution (both proved below). -/
noncomputable def shannonEntropy (p : V → ℝ) : ℝ :=
  -∑ i, klTerm (p i) 1

/-! ### Step 1: the term-wise information inequality and Gibbs' inequality -/

/-- The term-wise information inequality: one KL summand dominates
`a - b`. At `a = 0` this is `0 ≥ -b` (true since `0 < b`); otherwise it
is `Real.one_sub_inv_le_log_of_pos` at `a / b`, scaled by `a > 0`. This
single scalar lemma carries both `klDiv_nonneg` and (through its
strict companion `eq_of_klTerm_eq_sub`) the equality case. -/
theorem sub_le_klTerm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : a - b ≤ klTerm a b := by
  by_cases ha0 : a = 0
  · rw [ha0]
    simp only [klTerm, if_pos rfl, if_true]
    linarith
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    simp only [klTerm, if_neg ha0]
    have h1 : (1:ℝ) - b / a ≤ Real.log (a / b) := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hapos hb)
      rwa [inv_div] at h
    calc a - b = a * ((1:ℝ) - b / a) := by field_simp
      _ ≤ a * Real.log (a / b) := mul_le_mul_of_nonneg_left h1 (le_of_lt hapos)

/-- The strict companion: if a KL summand equals `a - b` exactly, then
`a = b`. Two independent sources of strictness meet here — at
`a = 0` the gap is `b > 0`, and otherwise `Real.log_lt_sub_one_of_pos`
at the reciprocal forces `a / b = 1`. This is what "Gibbs' inequality
is strict away from equality" is built from. -/
theorem eq_of_klTerm_eq_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h : klTerm a b = a - b) : a = b := by
  by_cases ha0 : a = 0
  · rw [ha0] at h
    simp only [klTerm, if_pos rfl, if_true] at h
    linarith
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    simp only [klTerm, if_neg ha0] at h
    by_contra hab
    have hx : a / b ≠ 1 := fun hh => hab ((div_eq_one_iff_eq (ne_of_gt hb)).mp hh)
    have hinv : (a / b)⁻¹ ≠ 1 := fun hh =>
      hx (by rw [← inv_inv (a / b), hh, inv_one])
    have hstrict : Real.log ((a / b)⁻¹) < (a / b)⁻¹ - 1 :=
      Real.log_lt_sub_one_of_pos (inv_pos.2 (div_pos hapos hb)) hinv
    rw [Real.log_inv, inv_div] at hstrict
    have h2 : (1:ℝ) - b / a < Real.log (a / b) := by linarith
    have h3 : a * ((1:ℝ) - b / a) < a * Real.log (a / b) :=
      mul_lt_mul_of_pos_left h2 hapos
    have h4 : a * ((1:ℝ) - b / a) = a - b := by field_simp
    rw [h4] at h3
    linarith

/-- **Gibbs' inequality** (the information inequality), nonnegative
direction: the relative entropy of a probability vector from a
strictly positive one is nonnegative. Summing `sub_le_klTerm`
term-wise gives `klDiv p q ≥ (∑ p) - (∑ q) = 0`. -/
theorem klDiv_nonneg {p q : V → ℝ} (hp : ∀ i, 0 ≤ p i) (hp' : ∑ i, p i = 1)
    (hq : ∀ i, 0 < q i) (hq' : ∑ i, q i = 1) : 0 ≤ klDiv p q := by
  have key : ∀ i ∈ (Finset.univ : Finset V), p i - q i ≤ klTerm (p i) (q i) :=
    fun i _ => sub_le_klTerm (hp i) (hq i)
  calc (0:ℝ) = (∑ i, p i) - ∑ i, q i := by rw [hp', hq', sub_self]
    _ = ∑ i, (p i - q i) := Finset.sum_sub_distrib.symm
    _ ≤ ∑ i, klTerm (p i) (q i) := Finset.sum_le_sum key
    _ = klDiv p q := rfl

/-- **Gibbs' inequality**, equality case: relative entropy vanishes
exactly when the distributions coincide. The forward direction
decomposes the (nonnegative, by `sub_le_klTerm`) per-index gap of the
sum and applies `eq_of_klTerm_eq_sub` at each index; the reverse
direction is `log 1 = 0` term-wise. Note the hypothesis `0 < q i` is
load-bearing in both directions: without it the statement is false
(`q` could concentrate where `p` does not). -/
theorem klDiv_eq_zero_iff {p q : V → ℝ} (hp : ∀ i, 0 ≤ p i) (hp' : ∑ i, p i = 1)
    (hq : ∀ i, 0 < q i) (hq' : ∑ i, q i = 1) : klDiv p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hgap : ∀ i ∈ (Finset.univ : Finset V), 0 ≤ klTerm (p i) (q i) - (p i - q i) :=
      fun i _ => sub_nonneg.mpr (sub_le_klTerm (hp i) (hq i))
    have hsumgap : ∑ i, (klTerm (p i) (q i) - (p i - q i)) = 0 := by
      have e1 : ∑ i, (klTerm (p i) (q i) - (p i - q i))
          = (∑ i, klTerm (p i) (q i)) - ∑ i, (p i - q i) := Finset.sum_sub_distrib
      have e2 : ∑ i, (p i - q i) = (∑ i, p i) - ∑ i, q i := Finset.sum_sub_distrib
      rw [e1, e2, show (∑ i, klTerm (p i) (q i)) = klDiv p q from rfl, h, hp', hq']
      ring_nf
    funext i
    have hz : klTerm (p i) (q i) - (p i - q i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hgap).mp hsumgap i (Finset.mem_univ i)
    exact eq_of_klTerm_eq_sub (hp i) (hq i) (sub_eq_zero.mp hz)
  · intro h
    subst h
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h0 : p i = 0
    · simp only [klTerm, if_pos h0]
    · simp only [klTerm, if_neg h0, div_self h0, Real.log_one, mul_zero]

/-! ### Step 2: the uniform bridge and the entropy maximum -/

/-- The uniform distribution on a nonempty `Fintype` sums to one
(at the real coercion of the cardinality). -/
theorem sum_inv_card_eq_one [Nonempty V] :
    ∑ _i : V, ((Fintype.card V : ℝ)⁻¹) = 1 := by
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : (∑ i : V, ((Fintype.card V : ℝ)⁻¹)) * (Fintype.card V : ℝ)
      = (1:ℝ) * (Fintype.card V : ℝ) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun _ _ => inv_mul_cancel₀ hn0),
      Finset.sum_const, Finset.card_univ, Nat.smul_one_eq_cast]
    simp
  exact mul_right_cancel₀ hn0 key

/-- Relative entropy against the uniform `n⁻¹`-distribution is exactly
the gap between `log n` and the Shannon entropy. This is the bridge
through which Gibbs' inequality becomes the entropy maximum; it is the
only place the two quantities meet. -/
theorem klDiv_apply_uniform {p : V → ℝ} (hp : ∀ i, 0 ≤ p i) (hp' : ∑ i, p i = 1)
    {n : ℝ} (hn : 0 < n) :
    klDiv p (fun _ => n⁻¹) = Real.log n - shannonEntropy p := by
  have step : ∀ i : V, klTerm (p i) n⁻¹ = klTerm (p i) 1 + p i * Real.log n := by
    intro i
    by_cases h0 : p i = 0
    · simp only [klTerm, h0, if_pos rfl]
      simp
    · have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm h0)
      simp only [klTerm, if_neg h0, div_inv_eq_mul]
      rw [Real.log_mul (ne_of_gt hpos) (ne_of_gt hn)]
      ring_nf
  calc klDiv p (fun _ => n⁻¹) = ∑ i, klTerm (p i) n⁻¹ := rfl
    _ = ∑ i, (klTerm (p i) 1 + p i * Real.log n) :=
        Finset.sum_congr rfl (fun i _ => step i)
    _ = (∑ i, klTerm (p i) 1) + (∑ i, p i) * Real.log n := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ i, klTerm (p i) 1) + Real.log n := by rw [hp', one_mul]
    _ = Real.log n - shannonEntropy p := by
        simp only [shannonEntropy]
        ring_nf

/-- The **entropy maximum bound**: Shannon entropy of a probability
vector on `V` is at most `log |V|` — Gibbs' inequality against the
uniform distribution, transported through `klDiv_apply_uniform`. The
`Nonempty V` side condition is derived, not assumed: an empty type
admits no probability vector. -/
theorem shannonEntropy_le_log_card {p : V → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp' : ∑ i, p i = 1) : shannonEntropy p ≤ Real.log (Fintype.card V) := by
  haveI hne : Nonempty V := by
    rcases (Finset.univ : Finset V).eq_empty_or_nonempty with h | h
    · exfalso
      rw [h] at hp'
      simp at hp'
    · obtain ⟨i, _⟩ := h
      exact ⟨i⟩
  have hn : (0:ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  have h := klDiv_nonneg (q := fun _ => (Fintype.card V : ℝ)⁻¹) hp hp'
    (fun _ => inv_pos.2 hn) sum_inv_card_eq_one
  rw [klDiv_apply_uniform hp hp' hn] at h
  linarith

/-- The entropy maximum's **equality case**: the bound
`shannonEntropy p ≤ log |V|` is attained exactly at the uniform
distribution. Both directions compose the Gibbs equality case with the
uniform bridge — strictness away from uniform is inherited from
`eq_of_klTerm_eq_sub`, not reproved. -/
theorem shannonEntropy_eq_log_card_iff {p : V → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp' : ∑ i, p i = 1) :
    shannonEntropy p = Real.log (Fintype.card V) ↔
      p = fun _ => (Fintype.card V : ℝ)⁻¹ := by
  haveI hne : Nonempty V := by
    rcases (Finset.univ : Finset V).eq_empty_or_nonempty with h | h
    · exfalso
      rw [h] at hp'
      simp at hp'
    · obtain ⟨i, _⟩ := h
      exact ⟨i⟩
  have hn : (0:ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  constructor
  · intro h
    have h0 : klDiv p (fun _ => (Fintype.card V : ℝ)⁻¹) = 0 := by
      rw [klDiv_apply_uniform hp hp' hn]
      linarith
    exact (klDiv_eq_zero_iff hp hp' (fun _ => inv_pos.2 hn)
      sum_inv_card_eq_one).mp h0
  · intro h
    have h0 : klDiv p (fun _ => (Fintype.card V : ℝ)⁻¹) = 0 :=
      (klDiv_eq_zero_iff hp hp' (fun _ => inv_pos.2 hn)
        sum_inv_card_eq_one).mpr h
    rw [klDiv_apply_uniform hp hp' hn] at h0
    linarith

/-- Shannon entropy is nonnegative: each `p i ≤ 1` (a single term of a
probability vector, by `Finset.single_le_sum`), so each negated
summand `p i * log (p i)` is nonnegative. -/
theorem shannonEntropy_nonneg {p : V → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp' : ∑ i, p i = 1) : 0 ≤ shannonEntropy p := by
  have hple : ∀ i : V, p i ≤ 1 := by
    intro i
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hp j)
      (Finset.mem_univ i)
    rwa [hp'] at h
  have hterm : ∀ i : V, klTerm (p i) 1 ≤ 0 := by
    intro i
    by_cases h0 : p i = 0
    · simp [klTerm, h0]
    · have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm h0)
      simp only [klTerm, if_neg h0, div_one]
      have hlog : Real.log (p i) ≤ 0 := by
        have h := Real.log_le_log hpos (hple i)
        rwa [Real.log_one] at h
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) hlog
  simp only [shannonEntropy]
  exact neg_nonneg.mpr (Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => hterm i)

/-! ## The entropy–χ² bridge -/

/-- Termwise entropy bound: one KL summand is at most `a·(a/b − 1)`,
by `log u ≤ u − 1` at `u = a/b` (the junk corner `a = 0` contributes
exactly `0`). The sum-level conversion to the χ² shape needs the two
mass hypotheses — see `klDiv_le_sum_sq_div`. -/
theorem klTerm_le_sub_one_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    klTerm a b ≤ a * (a / b - 1) := by
  by_cases ha0 : a = 0
  · rw [ha0]
    simp [klTerm, zero_mul]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    simp only [klTerm, if_neg ha0]
    have hlog : Real.log (a / b) ≤ a / b - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hapos hb)
    exact mul_le_mul_of_nonneg_left hlog (le_of_lt hapos)

/-- **The entropy–χ² bridge**: the relative entropy of a probability
vector from a strictly positive one is at most its χ² distance
`∑ (p − q)² / q`. The termwise bound gives `D ≤ ∑ p²/q − 1`, and the
two mass hypotheses identify `∑ p²/q − 1` with `∑ (p − q)²/q` — the
conversion is genuinely sum-level (termwise the shapes differ by
`b − a`, so the mass hypotheses are load-bearing). Stated in exactly
the sum shape the mixing layer's `chiSquareDistance` carries. -/
theorem klDiv_le_sum_sq_div {p q : V → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 < q i) (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    klDiv p q ≤ ∑ i, (p i - q i) ^ 2 / q i := by
  have hle : klDiv p q ≤ ∑ i, (p i * p i / q i - p i) :=
    Finset.sum_le_sum fun i _ =>
      (klTerm_le_sub_one_mul (hp i) (hq i)).trans_eq (by ring)
  rw [Finset.sum_sub_distrib, hp1] at hle
  have hsum : ∑ i, (p i - q i) ^ 2 / q i
      = ∑ i, p i * p i / q i - 1 := by
    calc ∑ i, (p i - q i) ^ 2 / q i
        = ∑ i, (p i * p i / q i - (2 * p i - q i)) :=
          Finset.sum_congr rfl fun i _ => by
            have h0 : q i ≠ 0 := ne_of_gt (hq i)
            field_simp
            ring
      _ = (∑ i, p i * p i / q i) - ∑ i, (2 * p i - q i) :=
            Finset.sum_sub_distrib
      _ = (∑ i, p i * p i / q i) - ((2:ℝ) * ∑ i, p i - ∑ i, q i) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (∑ i, p i * p i / q i) - 1 := by
            rw [hp1, hq1]
            norm_num
  rw [hsum]
  exact hle

/-! ## The two-block log-sum bound (Gibbs consumed) -/

/-- **The two-block log-sum inequality**, junk-safe: the KL summands
over a block dominate the single KL summand of the block sums. Proof:
rescale to the block-conditional probability vectors `u = p/a`,
`v = q/b` (each sums to one over `S`), split
`klTerm (a·u) (b·v) = a·u·log(a/b) + a·klTerm u v` termwise, and apply
Gibbs' inequality (`sub_le_klTerm`) on the block — the entropy
module's machinery composing its own Gibbs bound, the first such
internal consumption. -/
theorem sum_klTerm_ge_klTerm {V : Type*} (S : Finset V) {p q : V → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    klTerm (∑ i in S, p i) (∑ i in S, q i)
      ≤ ∑ i in S, klTerm (p i) (q i) := by
  rcases Finset.eq_empty_or_nonempty S with hS | hSn
  · subst hS
    simp [klTerm]
  obtain ⟨i₀, hi₀⟩ := hSn
  have hbpos : (0:ℝ) < ∑ i in S, q i :=
    Finset.sum_pos' (fun i _ => le_of_lt (hq i)) ⟨i₀, hi₀, hq i₀⟩
  by_cases ha : ∑ i in S, p i = 0
  · have hpz : ∀ i ∈ S, p i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => hp i)).mp ha
    have hR : ∑ i in S, klTerm (p i) (q i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [hpz i hi]
      simp [klTerm]
    rw [hR, ha]
    simp [klTerm]
  · have hapos : (0:ℝ) < ∑ i in S, p i :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hp i) (Ne.symm ha)
    obtain ⟨A, hAe⟩ : ∃ A, ∑ j in S, p j = A := ⟨_, rfl⟩
    obtain ⟨B, hBe⟩ : ∃ B, ∑ j in S, q j = B := ⟨_, rfl⟩
    have hA0 : (0:ℝ) < A := by rw [← hAe]; exact hapos
    have hB0 : (0:ℝ) < B := by rw [← hBe]; exact hbpos
    -- the per-term rescaling identity
    have hterm : ∀ i ∈ S,
        klTerm (p i) (q i)
          = A * Real.log (A / B) * (p i / A)
            + A * klTerm (p i / A) (q i / B) := by
      intro i hi
      by_cases hpi : p i = 0
      · have hl0 : klTerm (0 : ℝ) (q i) = 0 := by simp [klTerm]
        have hu0 : klTerm ((0:ℝ) / A) (q i / B) = 0 := by
          rw [zero_div]
          simp [klTerm]
        rw [hpi, hl0, hu0, zero_div, mul_zero]
        ring
      · have hpii : (0:ℝ) < p i :=
          lt_of_le_of_ne (hp i) (Ne.symm hpi)
        have hqi : (0:ℝ) < q i := hq i
        have hui : (0:ℝ) < p i / A := div_pos hpii hA0
        have hvi : (0:ℝ) < q i / B := div_pos hqi hB0
        simp only [klTerm, if_neg hpi, if_neg (ne_of_gt hui)]
        rw [Real.log_div (ne_of_gt hpii) (ne_of_gt hqi),
          Real.log_div (ne_of_gt hA0) (ne_of_gt hB0),
          Real.log_div (ne_of_gt hui) (ne_of_gt hvi),
          Real.log_div (ne_of_gt hpii) (ne_of_gt hA0),
          Real.log_div (ne_of_gt hqi) (ne_of_gt hB0)]
        field_simp
        ring
    -- sum the identity over S
    have hsumid : ∑ i in S, klTerm (p i) (q i)
        = A * Real.log (A / B) * ∑ i in S, (p i / A)
          + A * ∑ i in S, klTerm (p i / A) (q i / B) := by
      rw [Finset.sum_congr rfl (fun i hi => hterm i hi),
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hu1 : ∑ i in S, p i / A = 1 := by
      rw [← Finset.sum_div, hAe, div_self (ne_of_gt hA0)]
    have hv1 : ∑ i in S, q i / B = 1 := by
      rw [← Finset.sum_div, hBe, div_self (ne_of_gt hB0)]
    -- Gibbs on the block
    have hgibbs : (0:ℝ) ≤ ∑ i in S, klTerm (p i / A) (q i / B) := by
      have htermwise : ∀ i ∈ S,
          p i / A - q i / B ≤ klTerm (p i / A) (q i / B) :=
        fun i _ => sub_le_klTerm (div_nonneg (hp i) (le_of_lt hA0))
          (div_pos (hq i) hB0)
      calc (0:ℝ)
          = ∑ i in S, (p i / A - q i / B) := by
            rw [Finset.sum_sub_distrib, hu1, hv1, sub_self]
        _ ≤ ∑ i in S, klTerm (p i / A) (q i / B) :=
            Finset.sum_le_sum htermwise
    have hklab : klTerm A B = A * Real.log (A / B) := by
      have hAne : A ≠ 0 := by
        intro h
        exact ha (by rw [hAe, h])
      simp only [klTerm, if_neg hAne]
    rw [hAe, hBe, hklab, hsumid, hu1, mul_one]
    have hmul : (0:ℝ) ≤ A * ∑ i in S, klTerm (p i / A) (q i / B) :=
      mul_nonneg (le_of_lt hA0) hgibbs
    linarith

/-! ## The binary two-point bound (the FTC route) -/

/-- **The two-point bound, interior case**: for `0 < b ≤ a < 1`, the
binary divergence `d(a‖b)` dominates `2(a−b)²`. Route (a genuinely
second-order fact — the first-order scalar bounds `log t ≥ 1 − 1/t`
and `log t ≤ t − 1` provably cannot close it): the FTC identity
`d(a‖b) = ∫_b^a (a−t)/(t(1−t)) dt`, the integrand bounded below by
`4(a−t)` through AM-GM (`t(1−t) ≤ 1/4`), and
`∫_b^a 4(a−t) dt = 2(a−b)²`. -/
private theorem two_point_aux {a b : ℝ} (_ha : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 < b) (hba : b ≤ a) :
    2 * (a - b) ^ 2 ≤ klTerm a b + klTerm (1 - a) (1 - b) := by
  have hapos : (0:ℝ) < a := lt_of_lt_of_le hb hba
  have h1a : (0:ℝ) < 1 - a := sub_pos.2 ha1
  have h1b : (0:ℝ) < 1 - b := sub_pos.2 (lt_of_le_of_lt hba ha1)
  set F : ℝ → ℝ := fun t => a * Real.log t + (1 - a) * Real.log (1 - t)
    with hFdef
  set g : ℝ → ℝ := fun t => a * t⁻¹ - (1 - a) * (1 - t)⁻¹ with hgdef
  have hbox : Set.uIcc b a = Set.Icc b a := Set.uIcc_of_le hba
  -- the derivative identification on the whole closed box
  have hderiv : ∀ t ∈ Set.uIcc b a, HasDerivAt F (g t) t := by
    rw [hbox]
    intro t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le hb ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 ha1
    have h1 : HasDerivAt (fun t => a * Real.log t) (a * t⁻¹) t :=
      (Real.hasDerivAt_log (ne_of_gt ht0)).const_mul a
    have hconst : HasDerivAt (fun _ : ℝ => (1:ℝ)) (0:ℝ) t :=
      hasDerivAt_const t (1:ℝ)
    have hid0 : HasDerivAt (fun t : ℝ => t) (1:ℝ) t :=
      hasDerivAt_id t
    have hid : HasDerivAt (fun t => 1 - t) (-(1:ℝ)) t :=
      (hconst.sub hid0).congr_deriv (by norm_num)
    have hlogd : HasDerivAt (fun t : ℝ => Real.log (1 - t))
        ((-(1:ℝ)) / (1 - t)) t :=
      hid.log (sub_ne_zero.mpr (Ne.symm (ne_of_lt ht1)))
    have hconst2 : HasDerivAt (fun _ : ℝ => (1 - a)) (0:ℝ) t :=
      hasDerivAt_const t (1 - a)
    have h2 : HasDerivAt (fun t => (1 - a) * Real.log (1 - t))
        ((1 - a) * (-(1 - t)⁻¹)) t :=
      (hconst2.mul hlogd).congr_deriv (by
        have hne : (1:ℝ) - t ≠ 0 :=
          sub_ne_zero.mpr (Ne.symm (ne_of_lt ht1))
        field_simp)
    exact (h1.add h2).congr_deriv (by ring)
  have hcontg : ContinuousOn g (Set.uIcc b a) := by
    rw [hbox]
    have h1 : ContinuousOn (fun t => a * t⁻¹) (Set.Icc b a) :=
      ContinuousOn.mul continuousOn_const
        (ContinuousOn.inv₀ continuousOn_id (fun t ht =>
          ne_of_gt (lt_of_lt_of_le hb ht.1)))
    have h2 : ContinuousOn (fun t => (1 - a) * (1 - t)⁻¹) (Set.Icc b a) :=
      ContinuousOn.mul continuousOn_const
        (ContinuousOn.inv₀
          (ContinuousOn.sub continuousOn_const continuousOn_id)
          (fun t ht =>
            sub_ne_zero.mpr (Ne.symm (ne_of_lt (lt_of_le_of_lt ht.2 ha1)))))
    exact h1.sub h2
  -- FTC for F
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (ContinuousOn.intervalIntegrable hcontg)
  -- the value identification: the binary divergence is F a − F b
  have hkl : klTerm a b + klTerm (1 - a) (1 - b) = F a - F b := by
    simp only [klTerm, if_neg (ne_of_gt hapos), if_neg (ne_of_gt h1a),
      Real.log_div (ne_of_gt hapos) (ne_of_gt hb),
      Real.log_div (ne_of_gt h1a) (ne_of_gt h1b), hFdef]
    ring
  -- the comparison integrand: g t ≥ 4 (a − t) on the box
  have hpt : ∀ t ∈ Set.Icc b a, (fun t => 4 * (a - t)) t ≤ g t := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le hb ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 ha1
    have ht0' : t ≠ 0 := ne_of_gt ht0
    have ht1' : (1:ℝ) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt ht1))
    have hkey : g t - 4 * (a - t)
        = (a - t) * (2 * t - 1) ^ 2 / (t * (1 - t)) := by
      refine (eq_div_iff (mul_ne_zero ht0' ht1')).mpr ?_
      rw [hgdef]
      field_simp
      ring
    have hnn : (0:ℝ) ≤ g t - 4 * (a - t) := by
      rw [hkey]
      exact div_nonneg
        (mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg (2 * t - 1)))
        (mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr (le_of_lt ht1)))
    exact sub_nonneg.mp hnn
  -- FTC for the polynomial
  have hderiv2 : ∀ t ∈ Set.uIcc b a,
      HasDerivAt (fun t => 4 * a * t - 2 * (t * t)) (4 * (a - t)) t := by
    intro t _
    have h1 : HasDerivAt (fun t => 4 * a * t) (4 * a * (1:ℝ)) t :=
      (hasDerivAt_id t).const_mul (4 * a)
    have hsq : HasDerivAt (fun t : ℝ => t * t) (2 * t) t :=
      ((hasDerivAt_id t).mul (hasDerivAt_id t)).congr_deriv (by simp; ring)
    have h2 : HasDerivAt (fun t => 2 * (t * t)) (2 * (2 * t)) t :=
      hsq.const_mul 2
    exact (h1.sub h2).congr_deriv (by ring)
  have hcont2 : ContinuousOn (fun t => 4 * (a - t)) (Set.uIcc b a) :=
    ContinuousOn.mul continuousOn_const
      (ContinuousOn.sub continuousOn_const continuousOn_id)
  have hftc2 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2
    (ContinuousOn.intervalIntegrable hcont2)
  -- assemble
  calc 2 * (a - b) ^ 2
      = (fun t => 4 * a * t - 2 * (t * t)) a
          - (fun t => 4 * a * t - 2 * (t * t)) b := by
          show 2 * (a - b) ^ 2
            = 4 * a * a - 2 * (a * a) - (4 * a * b - 2 * (b * b))
          ring
    _ = ∫ t in b..a, (fun t => 4 * (a - t)) t := hftc2.symm
    _ ≤ ∫ t in b..a, g t :=
          intervalIntegral.integral_mono_on hba
            (ContinuousOn.intervalIntegrable hcont2)
            (ContinuousOn.intervalIntegrable hcontg)
            (fun t ht => hpt t ht)
    _ = klTerm a b + klTerm (1 - a) (1 - b) := by
          rw [hftc]
          exact hkl.symm

/-- **The two-point bound, top corner** `a = 1`: `log(1/b) ≥ 2(1−b)²`
by the same FTC route with the integrand `t⁻¹ ≥ 4(1−t)`. -/
private theorem two_point_top {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    2 * (1 - b) ^ 2 ≤ klTerm (1:ℝ) b + klTerm (1 - (1:ℝ)) (1 - b) := by
  have hbox : Set.uIcc b 1 = Set.Icc b 1 := Set.uIcc_of_le (le_of_lt hb1)
  have hderiv : ∀ t ∈ Set.uIcc b 1,
      HasDerivAt Real.log ((fun t => t⁻¹) t) t := by
    rw [hbox]
    intro t ht
    exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hb ht.1))
  have hcontg : ContinuousOn (fun t => t⁻¹) (Set.uIcc b 1) := by
    rw [hbox]
    exact ContinuousOn.inv₀ continuousOn_id (fun t ht =>
      ne_of_gt (lt_of_lt_of_le hb ht.1))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (ContinuousOn.intervalIntegrable hcontg)
  have hderiv2 : ∀ t ∈ Set.uIcc b 1,
      HasDerivAt (fun t => 4 * t - 2 * (t * t)) (4 * (1 - t)) t := by
    intro t _
    have h1 : HasDerivAt (fun t => 4 * t) (4 * (1:ℝ)) t :=
      (hasDerivAt_id t).const_mul (4:ℝ)
    have hsq : HasDerivAt (fun t : ℝ => t * t) (2 * t) t :=
      ((hasDerivAt_id t).mul (hasDerivAt_id t)).congr_deriv (by simp; ring)
    have h2 : HasDerivAt (fun t => 2 * (t * t)) (2 * (2 * t)) t :=
      hsq.const_mul 2
    exact (h1.sub h2).congr_deriv (by ring)
  have hcont2 : ContinuousOn (fun t => 4 * (1 - t)) (Set.uIcc b 1) :=
    ContinuousOn.mul continuousOn_const
      (ContinuousOn.sub continuousOn_const continuousOn_id)
  have hftc2 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2
    (ContinuousOn.intervalIntegrable hcont2)
  have hpt : ∀ t ∈ Set.Icc b 1,
      (fun t => 4 * (1 - t)) t ≤ (fun t => t⁻¹) t := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le hb ht.1
    have hkey : t⁻¹ - 4 * (1 - t) = (2 * t - 1) ^ 2 / t := by
      field_simp
      ring
    have hnn : (0:ℝ) ≤ t⁻¹ - 4 * (1 - t) := by
      rw [hkey]
      exact div_nonneg (sq_nonneg (2 * t - 1)) (le_of_lt ht0)
    exact sub_nonneg.mp hnn
  have hkl : Real.log 1 - Real.log b
      = klTerm (1:ℝ) b + klTerm (1 - (1:ℝ)) (1 - b) := by
    have h1 : klTerm (1:ℝ) b = -Real.log b := by
      simp only [klTerm, if_neg one_ne_zero, one_mul, one_div]
      rw [Real.log_inv]
    have h2 : klTerm (1 - (1:ℝ)) (1 - b) = 0 := by
      simp [klTerm]
    rw [Real.log_one, zero_sub, h1, h2, add_zero]
  calc 2 * (1 - b) ^ 2
      = (fun t => 4 * t - 2 * (t * t)) 1
          - (fun t => 4 * t - 2 * (t * t)) b := by
          show 2 * (1 - b) ^ 2
            = (4 * 1 - 2 * ((1:ℝ) * 1)) - (4 * b - 2 * (b * b))
          norm_num
          ring
    _ = ∫ t in b..1, (fun t => 4 * (1 - t)) t := hftc2.symm
    _ ≤ ∫ t in b..1, (fun t => t⁻¹) t :=
          intervalIntegral.integral_mono_on (le_of_lt hb1)
            (ContinuousOn.intervalIntegrable hcont2)
            (ContinuousOn.intervalIntegrable hcontg)
            (fun t ht => hpt t ht)
    _ = klTerm (1:ℝ) b + klTerm (1 - (1:ℝ)) (1 - b) := by
          rw [hftc]
          exact hkl

/-- **The binary two-point Pinsker bound**: `2(a−b)² ≤ d(a‖b)` for
`a ∈ [0,1]`, `b ∈ (0,1)` — symmetric under `(a,b) ↦ (1−a,1−b)`, so the
`b ≤ a` instances close both directions. -/
theorem klTerm_add_klTerm_one_sub_ge_two_sq {a b : ℝ} (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ klTerm a b + klTerm (1 - a) (1 - b) := by
  rcases le_or_lt b a with hba | hab
  · by_cases hatop : a = 1
    · subst hatop
      exact two_point_top hb hb1
    · exact two_point_aux ha (lt_of_le_of_ne ha1 hatop) hb hba
  · -- a < b: the mirrored pair (1−a, 1−b) satisfies b' ≤ a'
    have h1a : (0:ℝ) ≤ 1 - a := sub_nonneg.mpr ha1
    have h1b : (0:ℝ) < 1 - b := sub_pos.2 hb1
    have h1b1 : 1 - b < 1 := sub_lt_self (1:ℝ) hb
    have h1ba : 1 - b ≤ 1 - a := by linarith
    by_cases hz : a = 0
    · rw [hz]
      have hbt := two_point_top h1b h1b1
      have hid2 : klTerm (1 - (1:ℝ)) (1 - (1 - b)) = klTerm (0:ℝ) b := by
        simp only [sub_sub_self, sub_self]
      calc 2 * ((0:ℝ) - b) ^ 2 = 2 * (1 - (1 - b)) ^ 2 := by ring
        _ ≤ klTerm (1:ℝ) (1 - b) + klTerm (1 - (1:ℝ)) (1 - (1 - b)) :=
              hbt
        _ = klTerm (0:ℝ) b + klTerm (1 - (0:ℝ)) (1 - b) := by
              rw [hid2, sub_zero]
              exact add_comm _ _
    · have hapos : (0:ℝ) < a := lt_of_le_of_ne ha (Ne.symm hz)
      have h1a1 : 1 - a < 1 := sub_lt_self (1:ℝ) hapos
      have h := two_point_aux h1a h1a1 h1b h1ba
      have hid1 : (a - b) ^ 2 = ((1 - a) - (1 - b)) ^ 2 := by ring
      have hid2' : klTerm (1 - a) (1 - b)
          + klTerm (1 - (1 - a)) (1 - (1 - b))
          = klTerm a b + klTerm (1 - a) (1 - b) := by
        rw [sub_sub_self, sub_sub_self, add_comm]
      rw [hid1]
      exact h.trans_eq hid2'

end Scaffold.InformationTheory
