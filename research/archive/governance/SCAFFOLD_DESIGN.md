# Scaffold Design Policy

This document defines standards for creating high-quality scaffold files in this repository. Scaffolds are axiomatized mathematical statements intended as a foundation for future formalization work.

## Core Philosophy

**You are designing an API, not proving theorems.**

The goal is to create:
- Precise definitions for core objects
- Axioms with the right signatures
- Invariants that are preserved by updates
- Stable namespaces for eventual mathlib porting

Even if you never prove anything, getting the **interfaces** right makes the axioms usable as a dependency graph for downstream files.

## 1. Statement Shape: Never Use `True`

### Problem
`True` placeholders typecheck but block downstream reuse because later files cannot "use" the statement.

### Solution
Give every statement a *signature* that can compose, even if you don't want to commit to exact objects yet.

#### Bad
```lean
theorem laplacian_psd ... : True := by sorry
```

#### Good
```lean
theorem laplacian_psd
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnonneg : ∀ i j, 0 ≤ A i j) :
  ∀ x : V → ℝ, 0 ≤ quadForm (laplacian A) x := by sorry
```

#### Other Examples of Proper Shapes
- `Matrix.mulVec (laplacian A) onesVec = 0`
- `IsSelfAdjoint` or `Matrix.IsSymm` assumptions with `IsPosSemidef` conclusions
- `‖eventUpdate A u v w - A‖ ≤ C` for perturbation bounds

Even with `by sorry` proofs, the *shape* is what provides value.

## 2. Definitions Must Be Real

### Problem
Placeholder definitions make every theorem built on them meaningless.

### Required Real Definitions
These core objects MUST have actual implementations (not `0` or `True`):

- `deg` - degree of a vertex
- `degreeMatrix` - diagonal degree matrix
- `laplacian` - combinatorial Laplacian L = D - A
- `quadForm` - quadratic form xᵀ L x
- `rayleigh` - Rayleigh quotient R_L(x) = (xᵀ L x) / (xᵀ x)
- `conductance` - Cheeger ratio φ(S)
- `vol` - volume of a vertex set
- `boundary` - edge boundary weight
- `eventUpdate` - edge weight modification

### Implementation Pattern for Vectors
For vectors as functions `x : V → ℝ`:

```lean
/-- Quadratic form xᵀ L x -/
def quadForm (L : Matrix V V ℝ) (x : V → ℝ) : ℝ :=
  Matrix.dotProduct x (L.mulVec x)

/-- L² norm squared ⟨x, x⟩ -/
def normSq (x : V → ℝ) : ℝ :=
  ∑ i, x i * x i

/-- Rayleigh quotient with division-by-zero guard -/
def rayleigh (L : Matrix V V ℝ) (x : V → ℝ) : ℝ :=
  if h : normSq x ≠ 0 then
    quadForm L x / normSq x
  else
    0
```

This makes Cheeger, Poincaré, and lambda2 variational results consumable by other files.

## 3. Theorem vs Axiom Choice

### When to Use `axiom`
- Textbook facts you will never prove
- Statements from primary sources with precise citations
- Foundational properties you want to use but not prove

```lean
axiom cheeger_upper_bound
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnn : ∀ i j, 0 ≤ A i j) :
  conductance A ≤ Real.sqrt (2 * lambda2 A)
```

### When to Use `theorem ... := by sorry`
- Statements you might prove later
- Intermediate lemmas in development
- Anything experimental

Both are acceptable for scaffold work, but `axiom` is semantically honest for permanent postulates.

## 4. Graph Model Choice

### Pick One Primary Representation

**Option A: Matrix-first (recommended for spectral work)**
- Keep `WAdj := Matrix V V ℝ` as main type
- Add axioms about "graph-like adjacency":
  - Symmetry: `Matrix.IsSymm A`
  - Zero diagonal: `∀ i, A i i = 0`
  - Nonnegativity: `∀ i j, 0 ≤ A i j`

**Option B: SimpleGraph-first**
- Use `SimpleGraph V` as canonical
- Define `A` via `SimpleGraph.adjMatrix`
- Lift to weights later

For spectral graph theory and event-driven updates, **Option A is usually easier**.

### Import Discipline
- If you import `SimpleGraph` but use `WAdj` primarily, document which is primary
- Treat the secondary representation as a bridge with conversion lemmas

## 5. Guarded Definitions for Edge Cases

### Problem
Definitions like `D⁻¹` and `D^{-1/2}` fail on zero-degree vertices.

### Solutions

**Option 1: Add assumptions**
```lean
def transitionMatrix (A : WAdj) (hnonzero : ∀ i, deg A i ≠ 0) : Matrix V V ℝ :=
  (degreeMatrix A)⁻¹ * A
```

**Option 2: Define guarded inverse**
```lean
def invDeg (A : WAdj) (i : V) : ℝ :=
  if h : deg A i ≠ 0 then 1 / (deg A i) else 0

def transitionMatrix (A : WAdj) : Matrix V V ℝ :=
  fun i j => (invDeg A i) * A i j
```

**Option 3: Remove until ready**
Don't add definitions you can't make safe. You can always add them later.

## 6. Event Update Invariants

### Make Updates Preserve Structure by Construction

```lean
/-- A single event update to adjacency matrix (edge weight change). -/
def eventUpdate (A : WAdj (V:=V)) (u v : V) (w : ℝ) : WAdj (V:=V) :=
  fun i j =>
    if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then w else A i j

/-- Event updates preserve symmetry. -/
theorem eventUpdate_preserves_symmetry
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (u v : V) (w : ℝ) :
  Matrix.IsSymm (eventUpdate A u v w) := by
  sorry
```

This gives you a clean chain: "graph-like adjacency" invariant preserved by events.

## 7. File Organization Standards

### Single File Pattern
For small scaffolds (< 300 lines), a single file is fine.

### Multi-File Split Pattern
When growing beyond ~300 lines, split into focused files:

**Example: SpectralGraph/**
```
SpectralGraph/Basic.lean        - deg, Laplacian, quadForm, Rayleigh, invariants
SpectralGraph/Spectral.lean      - min-max, interlacing, Weyl, Davis–Kahan
SpectralGraph/Cheeger.lean       - conductance, Cheeger, Poincaré, mixing bounds
SpectralGraph/Dynamics.lean      - eventUpdate, stability under events, time-varying
```

Each file should:
- Import only what it needs
- Have a clear thematic focus
- Be usable independently

### Naming Conventions
- Files: `UpperCamelCase.lean`
- Namespaces: `UpperCamelCase` or `lower_snake_case` (match mathlib)
- Definitions/theorems: `lower_snake_case`

## 8. Namespace and Import Standards

### Namespace Structure
```lean
namespace SpectralGraphTheory
  -- definitions and theorems
end SpectralGraphTheory
```

Or for submodules:
```lean
namespace SpectralGraphTheory
  namespace Basic
    -- core definitions
  end Basic

  namespace Cheeger
    -- Cheeger-related theorems
  end Cheeger
end SpectralGraphTheory
```

### Import Style
```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
-- ... only what you need

open scoped BigOperators Matrix
open Classical
```

## 9. Documentation Standards

### Module Headers
Every file should have:
```lean
/-
  FileName.lean

  Purpose
  -------
  Brief description of what this file contains and why it exists.

  Notes
  -----
  * Important design decisions
  * Relationship to other files
  * TODOs for future work
-/
```

### Definition Documentation
```lean
/-- Degree of vertex `i` in adjacency matrix `A`.

This is the sum of weights of all edges incident to `i`.
-/
def deg (A : WAdj (V:=V)) (i : V) : ℝ :=
  ∑ j, A i j
```

### Axiom/Theorem Documentation
```lean
/-- Cheeger inequality upper bound: λ₂ ≤ 2 * h(G).

Source:
- Chung, "Spectral Graph Theory", AMS 1997
  Theorem 2.2, page 44

Intended meaning:
For any graph G, the second smallest eigenvalue λ₂ of the normalized
Laplacian is bounded above by twice the Cheeger constant h(G).
-/
axiom cheeger_upper_bound ...
```

## 10. Minimum Viable Axiom Set

### Don't Axiomatize Everything from a Book
Instead:
1. Define a small set of *core definitions* that are real
2. Add a moderately sized set of *axioms* you actually use repeatedly
3. Keep everything else out until you need it

This keeps the library lightweight and avoids time spent on unused axioms.

### Recommended Workflow
1. Start with definitions (deg, Laplacian, quadForm, rayleigh)
2. Add 5-10 core axioms you know you need
3. Only add more axioms when downstream work requires them
4. Remove unused axioms aggressively

## 11. Mathlib Compatibility

### Type Choices
- Prefer `Fin n` for fixed-size finite sets
- Prefer `V : Type* [Fintype V]` for generic finite types
- Use `Matrix V V ℝ` for adjacency matrices
- Use `Matrix.IsSymm` for symmetry (not `M.transpose = M`)

### Naming
- Follow mathlib naming conventions: `lower_snake_case`
- Use standard prefixes: `deg`, `vol`, `boundary`, `conductance`
- Match existing mathlib definitions when possible

## 12. Review Checklist

Before committing a scaffold file, verify:

- [ ] No `True` placeholders in theorem statements
- [ ] All core definitions have real implementations (not `0` or `True`)
- [ ] Event updates preserve invariants (symmetry, etc.)
- [ ] File is under 300 lines OR properly split
- [ ] Module header explains purpose and design decisions
- [ ] Namespace structure matches mathlib conventions
- [ ] Imports are minimal and explicit
- [ ] Axioms have citations (if applicable)
- [ ] Definitions have documentation
- [ ] Guarded edge cases (zero division, etc.)

## References

This policy draws from best practices discussed in `tips.md` and aligns with:
- Mathlib style guide
- The "API design, not theorem proving" philosophy
- Scaffold-specific needs for unproven but usable foundations
