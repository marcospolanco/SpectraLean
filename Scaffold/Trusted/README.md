# Trusted Layer

This directory contains the trusted layer of Scaffold.

## Policy

**IMPORTANT**: This directory is the ONLY place where `sorry` is allowed in Scaffold.

### Allowed Content

- `theorem := by sorry` - for experimental or work-in-progress results
- Policy documentation (this file)
- Internal testing and development tools

### Forbidden Content

- `axiom` declarations (should be in `Scaffold/Mathlib/**`)
- Public API theorems (should be in `Scaffold/Mathlib/**`)
- Results intended for downstream use

## Trust Boundaries

```
Scaffold/Mathlib/**  →  Public API (axiom only, no sorry)
Scaffold/Trusted/**   →  Quarantine zone (theorem := by sorry allowed)
```

## Migration Path

When moving from Trusted to Public API:

1. Replace `theorem := by sorry` with `axiom`
2. Add full documentation and citation
3. Move to appropriate location in `Scaffold/Mathlib/**`
4. Update index files

## Examples

### Correct (in Trusted/)
```lean
-- Experimental work
theorem experimental_result (X : RV Ω) : P(X > 0) ≤ 1 := by sorry
```

### Incorrect (should be in Mathlib/)
```lean
-- Public API axiom should not use sorry
axiom public_theorem (X : RV Ω) : P(X > 0) ≤ 1 := by sorry  -- WRONG!
```

### Correct (in Mathlib/)
```lean
-- Public API uses axiom without sorry
axiom public_theorem (X : RV Ω) : P(X > 0) ≤ 1
```

## See Also

- [Axiom Policy](../../../../governance/AXIOM_POLICY.md)
- [Contributing Guidelines](../../../../governance/CONTRIBUTING.md)
