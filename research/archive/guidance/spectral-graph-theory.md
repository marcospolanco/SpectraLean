# Spectral Graph Theory Scaffold Guidance

Domain-specific guidance for creating spectral graph theory scaffolds. This complements the general quality criteria in `governance/QUALITY_CRITERIA.md`.

## Core Definitions (Required)

These definitions MUST have real implementations:

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

**Why:** Cheeger, Poincaré, and λ₂ variational results require these to be consumable by other files.

## Graph Model: Matrix-First Approach

Use `WAdj := Matrix V V ℝ` as the primary representation with these invariants:

- Symmetry: `Matrix.IsSymm A`
- Zero diagonal: `∀ i, A i i = 0`
- Nonnegativity: `∀ i j, 0 ≤ A i j`

**Why:** Event-driven updates are easier with matrix representation. SimpleGraph can be added as a bridge later via `adjMatrix`.

## Guarded Definitions for Edge Cases

Normalized Laplacian and transition matrix require zero-degree handling:

**Option 1: Guarded inverse**
```lean
def invDeg (A : WAdj) (i : V) : ℝ :=
  if h : deg A i ≠ 0 then 1 / (deg A i) else 0

def transitionMatrix (A : WAdj) : Matrix V V ℝ :=
  fun i j => (invDeg A i) * A i j
```

**Option 2: Explicit assumption**
```lean
def transitionMatrix (A : WAdj) (hnonzero : ∀ i, deg A i ≠ 0) : Matrix V V ℝ :=
  (degreeMatrix A)⁻¹ * A
```

**Why:** Prevents accumulating theorems that break when refined.

## Event Update Invariants

Event updates must preserve graph structure:

```lean
/-- Edge weight modification -/
def eventUpdate (A : WAdj (V:=V)) (u v : V) (w : ℝ) : WAdj (V:=V) :=
  fun i j =>
    if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then w else A i j

/-- Updates preserve symmetry -/
theorem eventUpdate_preserves_symmetry
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (u v : V) (w : ℝ) :
  Matrix.IsSymm (eventUpdate A u v w) := by
  sorry
```

**Why:** Enables "static → event-driven" bridge for liquid graphs.

## Critical Axiom Shapes

Two axioms need proper shapes (not `True`):

### 1. Event Update Perturbation Bound
```lean
axiom eventUpdate_bounded
  (A : WAdj (V:=V)) (u v : V) (w : ℝ) :
  ‖eventUpdate A u v w - A‖ ≤ C
```
where `C` depends on weight bounds.

### 2. Spectral Persistence Under Events
```lean
axiom spectral_persistence_under_events
  (A : WAdj (V:=V)) (u v : V) (w : ℝ)
  (hA : Matrix.IsSymm A) :
  DavisKahanStability (eventUpdate A u v w) A (spectralGap A)
```

**Why:** These are the bridge between static spectral theory and event-driven liquid graphs.

## Axiom vs Theorem Choice

Use `axiom` for:
- Textbook facts with precise citations
- Foundational properties you won't prove
- Domain-specific postulates

Use `theorem ... := by sorry` for:
- Statements you might prove later
- Intermediate lemmas
- Experimental work

**Example:**
```lean
axiom cheeger_upper_bound
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnn : ∀ i j, 0 ≤ A i j) :
  lambda2 A ≤ 2 * cheegerConstant A
```

## Minimum Viable Axiom Set

Start with 5-10 core axioms you actually use:

1. Laplacian symmetry
2. Laplacian positive semidefiniteness
3. Ones vector in kernel
4. Cheeger inequalities (upper/lower)
5. Event update perturbation bound
6. Spectral persistence under events

Add more only when downstream work requires them.

## References

For detailed citation requirements, see `governance/AXIOM_POLICY.md`.

For general quality standards, see `governance/QUALITY_CRITERIA.md`.
