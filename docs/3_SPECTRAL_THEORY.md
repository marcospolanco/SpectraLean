# Spectral Theory and Algorithmic Pipeline

**Status:** Canonical research overview  
**Last reviewed:** August 17, 2026

This pillar separates the mathematical hypothesis, its formal dependencies, and the proposed software pipeline. Nothing labeled “hypothesis” below should be read as a proved result.

## 1. Dynamic-network model

Let a network at time step `k` have weighted adjacency matrix `Aₖ` and Laplacian `Lₖ`. An event stream changes the network by matrices `Eₖ`, so that, depending on the chosen representation,

```text
Aₖ₊₁ = Aₖ + Eₖ
```

and the Laplacian changes accordingly. The matrix-first representation is intentional: it exposes symmetry, norms, quadratic forms, eigenspaces, and low-rank updates directly. Applications must still specify whether edges are signed, directed, weighted, or multilayer; the current core primarily models finite real matrices and symmetric updates.

## 2. The “oil and water” hypothesis

The motivating hypothesis is that a coherent spectral subspace can retain its identity under a sequence of sufficiently small network events. In schematic form,

```text
‖Σₖ Eₖ‖ / γ < C
```

where `γ` is a relevant spectral separation and `C` depends on the perturbation theorem, norm, event model, and desired error tolerance. This expression is a design mnemonic, not a complete theorem: a valid statement must define the matrix being perturbed, the projector or invariant subspace being compared, the probability model, and every regularity assumption.

The proposed proof architecture is:

1. Use deterministic perturbation results such as Weyl and Davis–Kahan to convert an operator-norm bound into eigenvalue or subspace stability.
2. Use matrix concentration to control the cumulative random perturbation when event assumptions justify it.
3. Connect adjacency updates to Laplacian updates and account for degree changes.
4. Translate projector stability into an application-level identity or coordination criterion.

Steps 1 and 2 have cited axiom-level interfaces in Scaffold. The full chain, particularly steps 3 and 4 for the intended application, remains a research program.

## 3. Formalization boundary

| Component | Intended status |
| --- | --- |
| Real matrix, norm, quadratic-form, and Laplacian definitions | Real Lean definitions where implemented |
| Published concentration and perturbation results | Explicit cited axioms until proved upstream |
| Small consequences and compatibility checks | Fully proved QA lemmas |
| Dynamic subspace-persistence theorem | Research target; do not present as established |
| Application semantics for “identity” or “coordination” | Domain model requiring validation |

The implementation must avoid constant placeholder definitions for mathematical objects. It must also state symmetry, positivity, independence, boundedness, and nonzero-gap assumptions rather than relying on prose.

## 4. x90 coordination-detection pipeline

x90 is a proposed detector based on the evolution of a graph’s spectrum. Its core flow is:

```text
events or snapshots
        ↓
weighted graph A(t)
        ↓
Laplacian L(t)
        ↓
selected eigenvalues / spectral density
        ↓
spectral entropy H(t), rate dH/dt, truncation error
        ↓
normalized score and regime classification
```

### Inputs

- Time-stamped graph snapshots or edge events.
- A graph-construction policy, including windowing and edge weights.
- Observation scales and numerical tolerances.
- A normalization and threshold calibration policy.

### Outputs

- Spectral entropy and its estimated rate of change.
- A truncation-error or approximation-quality indicator.
- A normalized coordination score.
- A regime label with enough metadata to reproduce the classification.

### Operational constraints

- Graph construction can dominate the result; it must be versioned with the model.
- Sparse eigensolvers reduce cost but introduce truncation and convergence questions.
- Thresholds require calibration against relevant null and alternative data, not intuition alone.
- Spectral similarity is not semantic identity. Evaluation must include false positives, adversarial structures, and temporal confounders.
- The detector should expose uncertainty or quality flags when the eigensolver, truncation bound, or input window is inadequate.

## 5. Validation program

The research pipeline should advance through four gates:

1. **Mathematical shape:** all objects and assumptions are explicit; edge cases are defined.
2. **Formal interface:** the required results typecheck, carry citations, and have meaningful QA consequences.
3. **Numerical validation:** reference implementations agree on small graphs and controlled perturbations.
4. **Domain validation:** calibrated experiments demonstrate useful discrimination on held-out data.

A result must report which gate it has passed. Lean compilation alone does not establish numerical stability or empirical validity.

## 6. Immediate proof obligations

- Define the precise cumulative perturbation and norm used in the persistence ratio.
- Relate adjacency events to Laplacian perturbations with degree effects included.
- Choose projector-based or angle-based subspace distance and align it with the Davis–Kahan API.
- State the event independence or martingale assumptions needed by the selected concentration bound.
- Prove or axiomatize an end-to-end bound only after its constants and gap conditions are explicit.
- Connect the bound to x90 observables without equating a proxy with the target phenomenon.

## Source provenance

This document distills the archived [oil strategy](../research/archive/oil-strategy.md), [x90 specification](../research/archive/x90-algorithm.md), [spectral research transcript](../research/archive/chd-specral-10x.md), and [spectral graph guidance](../research/archive/guidance/spectral-graph-theory.md). The archived files contain exploratory detail and are not current claims of project status.
