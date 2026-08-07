# Scaffold Quality Criteria

This document defines the evaluation criteria for assessing scaffold file quality. Every scaffold file in this repository should be evaluated against these standards.

## Purpose

Ensure the repository grows in an opinionated, consistent way by providing objective quality criteria that can be applied to any scaffold file.

---

## 1. Definition Quality (25 points)

### 1.1 Core Definitions Are Real (10 points)
- [ ] **No placeholder definitions** returning `0` or `True` for core objects
- [ ] Mathematical objects are **executable in Lean**, not just stated
- [ ] Definitions use **mathlib-compatible types** (`Matrix`, `Finset`, etc.)

**What to check:** Look for `def`, not `noncomputable def` returning constant values.

**Examples of good definitions:**
```lean
def deg (A : WAdj) (i : V) : ℝ := ∑ j, A i j
def quadForm (L : Matrix V V ℝ) (x : V → ℝ) : ℝ := Matrix.dotProduct x (L.mulVec x)
```

**Examples of bad definitions:**
```lean
def quadForm (L : Matrix V V ℝ) (x : V → ℝ) : ℝ := 0  -- FAIL
def rayleigh (L : Matrix V V ℝ) (x : V → ℝ) : ℝ := True  -- FAIL
```

### 1.2 Edge Cases Are Guarded (8 points)
- [ ] Division operations have **zero-checks** or assumptions
- [ ] Matrix inverses have **invertibility conditions** or use guarded definitions
- [ ] Partial functions have **fallback values** documented

**What to check:** Look for `if h : ... ≠ 0 then ... else` patterns or explicit assumptions.

### 1.3 Type Abstraction Appropriate (7 points)
- [ ] **Prefer `V : Type [Fintype V]`** over `Fin n` for flexibility (unless domain requires fixed size)
- [ ] Use **mathlib type classes** appropriately (`Fintype`, `DecidableEq`)
- [ ] **Type variables are consistent** across the file (don't mix `Fin n` and `V` unnecessarily)

---

## 2. Statement Shape Quality (25 points)

### 2.1 No True Placeholders (12 points)
- [ ] **No theorem/axiom concludes with `True`**
- [ ] Every statement has a **meaningful mathematical conclusion**
- [ ] Even `sorry` proofs have **real types** that can be used downstream

**What to check:** Search for `: True` in theorem/axiom statements.

**Bad:**
```lean
theorem cheeger_upper_bound ... : True := by sorry
```

**Good:**
```lean
theorem cheeger_upper_bound ... : lambda2 A ≤ 2 * cheegerConstant A := by sorry
```

### 2.2 Assumptions Are Explicit (8 points)
- [ ] **Symmetry assumptions** are explicit: `Matrix.IsSymm M` (not `M.transpose = M`)
- [ ] **Nonnegativity assumptions** are stated: `∀ i j, 0 ≤ A i j`
- [ ] **Regularity/connectivity** assumptions are explicit when needed
- [ ] No **hidden preconditions** in definitions

### 2.3 Conclusions Are Composable (5 points)
- [ ] Theorems state **relations between objects**, not just properties
- [ ] Conclusions use **mathlib predicates** (`IsPosSemidef`, etc.) when available
- [ ] Statements are **usable in chains of reasoning**

---

## 3. API Design Quality (20 points)

### 3.1 File Organization (6 points)
- [ ] **Single file under 300 lines** or properly split into focused modules
- [ ] **Split pattern follows thematic boundaries** (e.g., Basic, Spectral, Cheeger, Dynamics)
- [ ] Each file is **usable independently** with minimal dependencies
- [ ] File names use **`UpperCamelCase.lean`** convention

**When to split:** If a scaffold grows beyond ~300 lines, organize by topic:
- `Domain/Basic.lean` - Core definitions and invariants
- `Domain/Spectral.lean` - Min-max, interlacing, perturbation bounds
- `Domain/Cheeger.lean` - Conductance, inequalities, mixing bounds
- `Domain/Dynamics.lean` - Event updates, stability under perturbations

Each file should import only what it needs and have a clear thematic focus.

### 3.2 Naming Conventions (7 points)
- [ ] Definitions/theorems use **`lower_snake_case`**
- [ ] Names are **descriptive but concise**
- [ ] **Consistent naming patterns** within domain (e.g., `deg`, `vol`, `boundary` for graphs)
- [ ] Namespace name **matches the file topic**

### 3.3 Namespace Structure (7 points)
- [ ] **Single primary namespace** for the module (e.g., `SpectralGraphTheory`)
- [ ] No orphaned definitions outside namespace (except imports)
- [ ] Namespace structure matches file organization when split

### 3.4 Minimal Surface Area (7 points)
- [ ] Definitions are **only what's needed** for the domain
- [ ] No "kitchen sink" axiomatization of entire textbooks
- [ ] **Focused scope** (e.g., spectral graph theory, not all graph theory)
- [ ] TODOs indicate **planned extensions**, not missing core functionality

---

## 4. Mathlib Compatibility (15 points)

### 4.1 Type Usage (8 points)
- [ ] Uses **`Matrix.IsSymm`** instead of `M.transpose = M`
- [ ] Uses **`Matrix.dotProduct`**, **`Matrix.mulVec`** for vector operations
- [ ] Uses **`Finset`** for finite sets, not hand-rolled set types
- [ ] Uses **standard real/number types** from mathlib

### 4.2 Import Hygiene (7 points)
- [ ] **Imports are minimal** (no unused imports)
- [ ] **No `import Mathlib`** blanket imports
- [ ] `open scoped` used for **specific scopes** (`BigOperators`, `Matrix`)
- [ ] `open Classical` is **explicit**, not hidden

---

## 5. Documentation Quality (10 points)

### 5.1 Module Headers (5 points)
- [ ] Every file has **header with Purpose/Notes**
- [ ] **Design decisions explained** (why `V` vs `Fin n`, etc.)
- [ ] **Relationships to other files** documented
- [ ] **Known limitations** noted (e.g., "zero-degree vertices not handled")

### 5.2 Definition Documentation (5 points)
- [ ] **Core definitions have doc comments** (`/-- ... -/`)
- [ ] Mathematical meaning is **clear from doc or name**
- [ ] **Axioms cite sources** when applicable (Author, Title, Theorem)
- [ ] **Non-obvious design choices** are explained in comments

---

## 6. Event-Driven Design (5 points)

### 6.1 Update Invariants (5 points)
- [ ] If domain has **dynamic updates**, they're defined
- [ ] **Structure-preserving updates** are explicit (e.g., symmetry preserved)
- [ ] **Perturbation bounds** are stated (even as axioms)
- [ ] **Spectral persistence** under updates is addressed

**Not applicable:** If the domain is purely static, this category is N/A and scored out of 95.

---

## Scoring Guidelines

### Excellent (90-100 points)
- All core definitions are real and executable
- Zero `True` placeholders
- Mathlib-compatible throughout
- Comprehensive documentation
- Event-driven invariants (if applicable)

### Good (75-89 points)
- Minor placeholders in non-core definitions
- Most statements have proper shapes
- Generally mathlib-compatible
- Documentation present but may lack detail

### Needs Work (60-74 points)
- Several core definitions are placeholders
- Multiple `True` placeholders
- Inconsistent naming or namespace usage
- Minimal documentation

### Reject (< 60 points)
- Core mathematical objects are placeholders
- Widespread use of `True` conclusions
- Not mathlib-compatible
- No documentation

---

## Quick Checklist for Reviewers

Before accepting a scaffold file, verify:

```bash
# Check for True placeholders
grep -n ": True" <file>.lean

# Check for placeholder definitions
grep -n "exact 0" <file>.lean
grep -n "exact True" <file>.lean

# Check for blanket imports
grep -n "import Mathlib$" <file>.lean

# Verify module header exists
head -20 <file>.lean | grep -q "Purpose"
```

---

## Application Examples

### spectral-a.lean: 72/100 (Needs Work)
- ✅ Real definitions (deg, laplacian, etc.)
- ❌ Uses `Fin n` instead of generic `V`
- ❌ Multiple `True` placeholders
- ❌ Uses `transpose =` instead of `Matrix.IsSymm`

### spectral-b.lean: 65/100 (Needs Work)
- ✅ Generic `V` type
- ✅ Uses `Matrix.IsSymm`
- ❌ Many placeholder definitions (`0`, `True`)
- ❌ `True` conclusions in theorems

### spectral.lean: 82/100 (Good)
- ✅ Real definitions for core objects
- ✅ Generic `V` type with `Fintype`
- ✅ Uses `Matrix.IsSymm`
- ⚠️ Some `True` placeholders remain
- ✅ Event-driven schema present
- ✅ Module header and docs

---

## Relationship to Other Governance Documents

- **AXIOM_POLICY.md**: Focuses on citation and review process
- **SCAFFOLD_DESIGN.md**: Focuses on how to write scaffolds
- **QUALITY_CRITERIA.md** (this file): Focuses on how to **evaluate** scaffold quality

All three should be used together when creating or reviewing scaffold files.
