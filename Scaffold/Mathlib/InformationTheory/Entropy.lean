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

QA: `Scaffold/QA/InformationTheory/Entropy_QA.lean`.
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

end Scaffold.InformationTheory
