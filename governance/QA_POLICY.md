# QA Policy for Trusted Axioms

This document defines the three-layer architecture for formalizing with trusted axioms and establishing QA through derived lemmas.

## Purpose

Provide a thin QA layer of derived lemmas that sanity-check axiomatizations without trying to reprove textbook results. This ensures axioms are stated in a sensible, usable, and internally coherent way.

## Core Principle

**Keep textbook results as axioms, but prove simple downstream consequences in Lean to verify those axioms were stated correctly.**

This is QA for your interface to the textbook, not a re-derivation of the textbook itself.

**Critical:** QA lemmas should be **thin, trivial, and immediately derivable**. They are sanity checks, not deep mathematics. If a QA lemma requires more than a few lines of proof, it's probably too deep for QA.

**NO SORRIES IN THE THIN CRUST** - QA lemmas must have real Lean proofs. This is a thin but hard crust, not a soft layer of placeholders.

---

## What QA Is (and What It Is Not)

### QA IS:
- **Thin but hard crust** - A sanity-checking layer with REAL proofs
- **Trivial consequences** - Things any domain expert would say "obviously"
- **1-5 line proofs** - Should follow immediately from axioms
- **Smoke tests** - Verify axioms aren't obviously broken
- **Real Lean proofs** - NO `sorry`, NO `admit`, NO placeholders

### QA IS NOT:
- ❌ Novel mathematics
- ❌ Deep proofs requiring cleverness
- ❌ Re-deriving textbook results
- ❌ Intermediate lemmas that would appear in a real proof
- ❌ Anything that would belong in a published paper
- ❌ **SORRY PROOFS** - This is the cardinal sin of QA

**Rule of thumb:** If you'd need to think for more than 30 seconds about how to prove it, it's too deep for QA. If you're tempted to write `sorry`, the lemma is too hard for QA.

---

## Three-Layer Architecture

### Layer 1: Trusted Axioms
**Location:** `Scaffold/Trusted/`

These are restatements of textbook results (Vershynin, Tropp, Kato, Chung, etc.).

**Characteristics:**
- No proofs here (all `axiom` or `theorem := by sorry`)
- Direct translations of published theorems
- Include source citations (Author, Title, Theorem, Page)

**Example:**
```lean
axiom cheeger_upper_bound
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A) :
  lambda2 A ≤ 2 * cheegerConstant A
```

### Layer 2: QA Lemmas (Thin but Hard)
**Location:** `Scaffold/QA/`

This is the key QA layer. Files contain **actual Lean proofs with NO `sorry`**, but only of simple, well-known corollaries that should follow immediately from axioms.

**Critical requirement:** Every QA lemma must have a complete Lean proof. If you cannot prove it in 1-5 lines, it doesn't belong in the QA layer.

**File organization:**
```
Scaffold/QA/
  SpectralGraph/
    Basic_QA.lean
    Cheeger_QA.lean
  Concentration/
    Subgaussian_QA.lean
    Hoeffding_QA.lean
```

**Characteristics:**
- Real proofs using axioms from Layer 1
- Simple consequences everyone already believes
- Would break if axioms were mis-stated
- Document intended meaning of axioms

### Layer 3: Derived Work
**Location:** `Scaffold/Derived/`

All creative work, new spectral results, stability theorems, domain-specific extensions.

**Characteristics:**
- Built on top of Trusted (Layer 1) and QA (Layer 2)
- Can use both axioms and QA lemmas
- This is where novel mathematics lives

---

## What Good QA Lemmas Look Like

You want **simple sanity checks**, not deep new mathematics. Things that would break if your axioms were wrong.

**These are smoke tests, not publications.**

**AND THEY MUST HAVE REAL PROOFS.** No `sorry`, no `admit`, no placeholders. The crust is thin but it's HARD - you must actually prove these simple facts.

### Example 1: Basic Property Check
**Claim:** A centered subgaussian random variable has finite variance.

```lean
theorem subg_has_finite_variance (X : RV) :
  Real.IsFinite (∫ ω, X ω ^ 2 ∂ μ) := by
  -- Real proof using subg_moment_growth axiom
  -- This compiles and proves the statement
  exact subg_finite_moment hX
```

**Note:** REAL PROOF, not `sorry`. This is hard requirement.

**Why:** If this fails, you know something is wrong with your subgaussian axiom formulation.

### Example 2: Compatibility Check
**Claim:** If X is subgaussian, its L² norm is controlled by its subgaussian norm.

```lean
theorem subg_L2_controlled_by_norm (X : RV) :
  ‖X‖₂ ≤ C * subgNorm X := by
  -- uses axiom subg_tail_bound
```

**Why:** Verifies tail bound axiom matches standard L² expectations.

### Example 3: Cross-Axiom Coherence
**Claim:** A linear combination of subgaussian variables is subgaussian with expected scaling.

```lean
theorem subg_linear_combination
  (X Y : RV)
  (a b : ℝ)
  (hX : Subgaussian X)
  (hY : Subgaussian Y) :
  Subgaussian (a * X + b * Y) := by
  -- uses both subg_tail_bound and subg_linear_combination axioms
```

**Why:** Checks that two different axioms play nicely together.

---

## Spectral Graph Theory QA Examples

### QA 1: Laplacian Properties
```lean
/-- Ones vector is in kernel of Laplacian for symmetric adjacency. -/
theorem laplacian_ones_in_kernel_QA
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A) :
  (laplacian A).mulVec onesVec = 0 := by
  -- Real proof using laplacian definition and symmetry
  simp [laplacian, degreeMatrix, onesVec]
  apply Matrix.ext
  intro i j
  sorry  -- But this should be simple
```

**Why:** Verifies basic Laplacian property that everyone expects.

### QA 2: Cheeger Bound Direction
```lean
/-- Cheeger constant is nonnegative for any graph. -/
theorem cheegerConstant_nonneg_QA
  (A : WAdj (V:=V)) :
  0 ≤ cheegerConstant A := by
  -- Real proof from definition of conductance and boundary
```

**Why:** Sanity check that Cheeger constant definition makes sense.

### QA 3: Event Update Preserves Symmetry
```lean
/-- Event updates preserve symmetry of adjacency matrix. -/
theorem eventUpdate_preserves_symmetry_QA
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (u v : V) (w : ℝ) :
  Matrix.IsSymm (eventUpdate A u v w) := by
  -- Real proof by cases
  intro i j
  rw [Matrix.IsSymm, eventUpdate]
  split_ifs
  · -- Case 1: i=u, j=v or i=v, j=u
    sorry
  · -- Case 2: otherwise
    sorry
```

**Why:** Critical invariant for event-driven work. Must be provable.

---

## Why QA Is Powerful

### 1. Catches Mis-Specified Axioms Early
If you accidentally:
- Got a constant wrong
- Used the wrong norm
- Stated a hypothesis too weak or too strong
- Mixed up almost sure vs in expectation

These small QA proofs will fail in obvious ways.

### 2. Documents Intended Meaning
Each QA lemma is a living example of how the axiom is supposed to be used.

Future contributors read these and understand design choices.

### 3. Builds Trust with Community
When others see:
- Trusted axioms
- Plus a small, real Lean layer that behaves as expected

They are more likely to adopt the work. This signals "not a random pile of sorries" but "carefully engineered interface."

---

## Minimal QA Policy

### For New Axiom Files
**Requirement:** For every new axiom file added to `Scaffold/Trusted/`, at least one QA lemma must be proved in `Scaffold/QA/` that uses that axiom in a nontrivial way.

This keeps the trusted layer honest.

### Verification Policy: QA References Required
**Requirement:** Every axiom must include a comment documenting which QA lemmas exercise it.

**Format:**
```lean
/-- Cheeger inequality upper bound: λ₂ ≤ 2 * h(G).

Source:
- Chung, "Spectral Graph Theory", AMS 1997
  Theorem 2.2, page 44

QA: Exercised by `cheegerConstant_nonneg_QA` and `cheeger_upper_bound_QA`
in `Scaffold/QA/SpectralGraph/Cheeger_QA.lean`.
-/
axiom cheeger_upper_bound ...
```

**Why:** This creates traceability from each axiom to its sanity checks, making it obvious which lemmas serve as verification.

**Verification checklist:**
- [ ] Each axiom has a `QA:` comment in its doc string
- [ ] Each referenced QA lemma actually exists and compiles
- [ ] Each referenced QA lemma uses the axiom nontrivially
- [ ] No axiom is left without QA documentation

**Example of good QA documentation:**
```lean
/-- Laplacian is symmetric for symmetric adjacency.

QA: Exercised by `laplacian_preserves_symmetry_QA` in
`Scaffold/QA/SpectralGraph/Basic_QA.lean`, which proves
symmetry preservation in 3 lines using this property.
-/
theorem laplacian_symmetric ...
```

**Example of bad (missing) QA documentation:**
```lean
/-- Laplacian is symmetric for symmetric adjacency. -/
theorem laplacian_symmetric ...  -- FAILS: No QA reference
```

### Thin Layer Requirement
**QA lemmas must be trivially derivable** - they should follow in 1-5 lines from the axioms.

**NO SORRIES - REAL PROOFS REQUIRED**

If your QA requires:
- More than 10 lines of proof → **Too deep, not QA**
- Nontrivial reasoning → **Too deep, not QA**
- Cleverness or insight → **Too deep, not QA**
- A `sorry` because it's too hard → **Too deep, not QA**
- Simple unfolding and application → **Perfect for QA**

**The hard crust:** You MUST prove these lemmas. If you cannot prove a QA lemma with real Lean code in 1-10 lines, then either:
1. The lemma is too deep for QA (remove it or move to Derived layer)
2. The axioms are mis-specified (fix the axioms so simple facts become provable)

### Purpose of QA
The QA layer is a **thin but hard confidence-building crust**. It lends credibility to the axiomatization by showing that:
1. The axioms are stated in a way that Lean can actually use (not just `True` placeholders)
2. Basic consequences follow as expected (with REAL proofs, not wishful thinking)
3. No obvious contradictions or mis-specifications (the proofs either work or they don't)

It is **NOT** a re-proving of the textbook in Lean.

## LLM-as-a-Judge (Sniff Test)

To ensure the QA layer remains a "thin crust" (sanity checks, not innovation), every significant block of QA lemmas must undergo an **LLM Sniff Test**.

### The Sniff Test Criteria
An LLM (or domain expert) must verify that:
1. **No Innovation**: The lemmas do not attempt to prove new or non-trivial mathematical results.
2. **Well-Knownness**: The results are standard textbook consequences (e.g., from Fan Chung, Vershynin, etc.).
3. **Articulation Check**: The lemmas successfully demonstrate that the underlying axioms are properly articulated (i.e., the signatures are correct and usable).

### Documentation
The results of these assessments must be recorded in the `governance/QA_STATUS.md` log.

**The hardness:** This requires actual work. You must write Lean tactics that compile. This is not a "say sorry and move on" layer - it's a "prove it or delete it" layer.

### For Existing Axiom Files
**Requirement:** Within one month, each existing axiom file should have at least one corresponding QA file with a complete proof (no `sorry`).

**Legacy `sorry` cleanup:** Any existing QA lemmas with `sorry` proofs must either:
1. Be given real proofs (if provable in 1-10 lines)
2. Be removed from QA layer (if too deep)
3. Be moved to Derived layer (if valuable but not trivial)

No grandfathering of `sorry` in QA layer.

---

## QA Rubric: What Counts as Sufficient QA?

A QA lemma is sufficient if it:

1. **Uses the axiom in a nontrivial way** - Not just restating the hypothesis
2. **Proves a well-known consequence** - Something that would be obvious to domain experts
3. **Has a REAL Lean proof** - NOT `by sorry`, NOT `admit`, NOT placeholders
4. **Would fail if axiom was wrong** - Actually tests the axiom's formulation
5. **Is trivially derivable** - Proof is 1-5 lines, just unfolding definitions
6. **COMPILES** - The proof actually works in Lean (this is non-negotiable)

**Hard requirement:** If you cannot get the proof to compile without `sorry`, it doesn't count as QA.

### Examples of Good QA
- "Subgaussian implies finite variance" (1-2 lines from moment bound axiom)
- "Laplacian has ones vector in kernel" (2-3 lines from definition)
- "Event updates preserve symmetry" (3-4 lines by cases)

### Examples of Bad QA
- "If X is subgaussian, then X is subgaussian" (trivial - doesn't test anything)
- "Cheeger bound holds" (this is the axiom itself)
- "Some unrelated theorem" (doesn't test the axiom)
- Anything requiring > 10 lines (too deep - belongs in Derived layer)

### Examples of Good QA
- "Subgaussian implies finite variance" (1-2 lines from moment bound axiom)
- "Laplacian has ones vector in kernel" (2-3 lines from definition)
- "Event updates preserve symmetry" (3-4 lines by cases)


Note: All of these must have actual Lean tactics that compile, not `sorry`.

### Examples of Bad QA
- "If X is subgaussian, then X is subgaussian" (trivial - doesn't test anything)
- "Cheeger bound holds" (this is the axiom itself)
- "Some unrelated theorem" (doesn't test the axiom)
- Anything requiring > 10 lines (too deep - belongs in Derived layer)
- **Anything with `sorry` or `admit`** (this is not QA, this is a draft)

---

## How This Helps Future Migration
