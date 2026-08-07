## Scaffold: full project specification

### 0. Project summary

**Scaffold** is an open source Lean library that provides a **mathlib compatible**, **textbook anchored**, **axiom level** foundation for modern applied mathematics.

* Classical results are **restated as axioms** (or sorries only in a quarantined layer) with **precise citations** to textbooks or primary sources.
* All **new work** built on top of those axioms should be **fully formal** (no sorry) in downstream projects, or in a separate `Derived` layer if you choose to host it in the same monorepo.
* Scaffold is designed to **future pace mathlib** by matching its namespace conventions and making it easy to replace axioms with real theorems as mathlib catches up.

Core goal: **maximum adoption** with disciplined transparency.

---

### 1. Non goals

* Scaffold does not aim to prove the cited theorems.
* Scaffold does not aim to replace mathlib.
* Scaffold does not aim to host copyrighted textbook text, figures, or large verbatim excerpts.
* Scaffold does not aim to be a dumping ground of unconstrained axioms. Every axiom must be minimal, cited, and scoped.

---

### 2. Audience

Primary adopters:

* Lean users in ML theory, applied probability, optimization, control, numerical linear algebra
* Formal methods practitioners who need modern inequalities and bounds quickly
* Researchers wanting mechanically checked “new reasoning” without formalizing decades of background

Secondary adopters:

* mathlib contributors who want a structured backlog of high impact results to formalize later

---

### 3. Core design principles

1. **Mathlib compatibility first**

   * Mirror mathlib’s directory layout and naming style.
   * Use mathlib types and structures whenever possible.
   * Avoid reinventing foundational definitions unless necessary.

2. **Assumptions are explicit**

   * Every nontrivial theorem included in Scaffold’s trusted layer is an `axiom` (preferred) or a `theorem := by sorry` only in a quarantined folder.

3. **Citations are first class**

   * Every axiom must include a precise citation comment: author, title, edition if relevant, chapter/section, theorem number and page if possible.
   * Maintain a separate human readable index mapping sources to axioms.

4. **Minimize blast radius**

   * Keep a small stable `Core` with shared definitions.
   * Prefer many small axioms to one big axiom.

5. **Replaceability**

   * Every axiom is intended to be replaced by a proved mathlib theorem in the future.
   * Provide a clear deprecation and migration policy.

---

### 4. Namespaces and import paths

#### 4.1 Recommended namespace strategy

Top level namespace: `Scaffold`

Inside it, a mathlib mirror subtree:

* `Scaffold.Mathlib.<same as Mathlib namespaces>`

Example:

* `Scaffold.Mathlib.Probability.Concentration.Subgaussian`
* `Scaffold.Mathlib.Probability.Concentration.Bernstein`
* `Scaffold.Mathlib.LinearAlgebra.RandomMatrix.MatrixBernstein`
* `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation`

Rationale:

* Downstream projects can switch imports from `Scaffold.Mathlib.*` to `Mathlib.*` with minimal changes.
* Scaffold stays conceptually subordinate and compatible, rather than a competing ecosystem.

#### 4.2 Optional split for derived work

If you want to host new theorems in the same repo (optional):

* `Scaffold.Derived.*` for fully proved, novel developments that rely on `Scaffold.Mathlib.*`

Strong recommendation for adoption: keep the initial repo focused on the trusted layer and indices, and encourage derived work in separate repos.

---

### 5. Repository layout

```
scaffold/
├── LICENSE
├── README.md
├── lakefile.lean
├── lake-manifest.json
├── Scaffold.lean                      # umbrella import (small)
├── Scaffold/
│   ├── Mathlib/
│   │   ├── Core/
│   │   │   ├── RandomVariable.lean
│   │   │   ├── Norms.lean
│   │   │   └── README.md
│   │   ├── Probability/
│   │   │   ├── Concentration/
│   │   │   │   ├── Scalar/
│   │   │   │   │   ├── Subgaussian.lean
│   │   │   │   │   ├── Subexponential.lean
│   │   │   │   │   ├── Hoeffding.lean
│   │   │   │   │   ├── Bernstein.lean
│   │   │   │   │   ├── Azuma.lean
│   │   │   │   │   ├── Freedman.lean
│   │   │   │   │   └── README.md
│   │   ├── LinearAlgebra/
│   │   │   ├── RandomMatrix/
│   │   │   │   ├── MatrixBernstein.lean
│   │   │   │   ├── MatrixHoeffding.lean
│   │   │   │   ├── GaussianSpectralNorm.lean
│   │   │   │   └── README.md
│   │   ├── Analysis/
│   │   │   ├── OperatorTheory/
│   │   │   │   ├── Perturbation/
│   │   │   │   │   ├── DavisKahan.lean
│   │   │   │   │   ├── ResolventBounds.lean
│   │   │   │   │   ├── SpectralProjectors.lean
│   │   │   │   │   └── README.md
│   ├── Trusted/
│   │   └── README.md                  # policy and warnings
│   └── Internal/
│       ├── Style.lean                 # shared simp sets, notation if needed
│       └── README.md
├── index/
│   ├── sources/
│   │   ├── vershynin_hdp.md
│   │   ├── wainwright_hds.md
│   │   ├── tropp_tail_bounds.md
│   │   └── README.md
│   ├── map/
│   │   ├── probability_concentration.md
│   │   ├── random_matrix.md
│   │   ├── perturbation.md
│   │   └── README.md
│   └── load_bearing_axioms.md
├── governance/
│   ├── CONTRIBUTING.md
│   ├── CODE_OF_CONDUCT.md
│   ├── MAINTAINERS.md
│   ├── AXIOM_POLICY.md
│   ├── DEPRECATION_POLICY.md
│   └── RELEASES.md
├── scripts/
│   ├── lint_axioms.py                 # optional
│   └── check_citations.py             # optional
└── .github/
    ├── workflows/
    │   ├── ci.yml
    │   └── lint.yml
    └── ISSUE_TEMPLATE/
        ├── axiom_request.md
        └── bug_report.md
```

Notes:

* `Scaffold/Mathlib/**` is the public API.
* `Scaffold/Trusted/**` holds policies. If you include any `sorry` at all, it must live under `Scaffold/Trusted/**` and never leak into `Scaffold/Mathlib/**`.
* `index/**` is critical for adoption and credibility.

---

### 6. Build system and toolchain

Use `lake` with mathlib dependency.

#### 6.1 lakefile requirements

* Scaffold must depend on a pinned mathlib version (tag or commit).
* Provide an easy update path in `governance/RELEASES.md`.

#### 6.2 CI requirements

CI must:

* build the whole project
* run `lake exe cache get` if using mathlib cache
* fail on any file that introduces `sorry` outside `Scaffold/Trusted/**`
* optionally run a citation linter

---

### 7. Public API policy

#### 7.1 What counts as public API

Everything under `Scaffold.Mathlib.*` is public and versioned.

#### 7.2 API stability rules

* Do not break names or signatures casually.
* If a change is necessary, follow the deprecation policy and provide a migration note.

---

### 8. Content policy: axioms, sorries, and definitions

#### 8.1 Preferred mechanism: `axiom`

Use `axiom` for textbook results.

Benefits:

* explicit, fast, unambiguous
* avoids accidental proof obligations
* signals trusted boundary clearly

#### 8.2 Allowed mechanism: `theorem := by sorry` only in quarantine

Only allowed in:

* `Scaffold/Trusted/**`

Never allowed in:

* `Scaffold/Mathlib/**`

Reason:

* Keeps the public API clean and makes trust boundaries obvious.

#### 8.3 Definitions policy

* Put shared definitions in `Scaffold.Mathlib.Core`.
* Use existing mathlib definitions whenever possible.
* If you introduce a new definition, document:

  * motivation
  * alternative equivalent definitions
  * stability expectation

---

### 9. Documentation and citation requirements

Each axiom must include:

1. A doc comment stating intent in plain language.
2. A citation block with:

   * author
   * title
   * edition/year (if relevant)
   * location (chapter/section/theorem number, page if possible)
3. A short note about how the Lean statement matches the math statement.

Example doc comment template:

```lean
/--
Tail bound for a subgaussian random variable.

Source:
- Vershynin, High Dimensional Probability, 2nd ed.
  Theorem 2.1.1, Chapter 2.

Intended meaning:
This axiom states the standard subgaussian tail inequality in a form suitable for downstream bounds.
-/
axiom subgaussian_tail_bound : ...
```

Also update:

* the corresponding `index/sources/<source>.md`
* the corresponding `index/map/<area>.md`

---

### 10. Naming conventions

Follow mathlib conventions:

* theorem names: lower snake case
* avoid brand specific names in theorem identifiers
* keep names descriptive and stable

Examples:

* `subgaussian_tail_bound`
* `hoeffding_inequality`
* `bernstein_inequality`
* `matrix_bernstein`
* `davis_kahan_sin_theta`

---

### 11. Initial scope for maximum adoption

Phase 1 focuses on modern probability concentration, then expands.

#### 11.1 Phase 1 modules

**Scalar concentration**

* Subgaussian basics: Orlicz norm, tails, moment growth, linear combinations
* Subexponential basics
* Hoeffding inequality
* Bernstein inequality
* Azuma inequality
* Freedman inequality (martingale Bernstein)

**Matrix concentration**

* Matrix Hoeffding
* Matrix Bernstein (Tropp style)
* Gaussian spectral norm bounds (basic)

These are the “adoption magnet” modules.

#### 11.2 Phase 2 modules

**Random matrix and high dimensional stats**

* Hanson Wright (if feasible as axioms)
* basic bounds for sample covariance (nonasymptotic)
* union bounds, chaining placeholders (careful scope)

**Graph spectra and perturbation**

* Davis Kahan
* resolvent bounds
* spectral projector stability

---

### 12. Detailed module specifications

Below are concrete file level specs for the first wave.

#### 12.1 `Scaffold/Mathlib/Core/RandomVariable.lean`

Purpose:

* Provide minimal shared notion of a real random variable tied to a probability measure.
* Avoid inventing a whole probability layer.

Requirements:

* Use mathlib’s measure theory and probability measure types.
* Provide a simple alias:

```lean
def RV (Ω : Type) [MeasurableSpace Ω] := Ω → ℝ
```

Optionally parameterize by measure `μ` in theorem statements.

#### 12.2 `Scaffold/Mathlib/Probability/Concentration/Scalar/Subgaussian.lean`

Axioms to include (minimum set):

1. `subgaussian_norm : (Ω → ℝ) → ℝ` (Orlicz style, but abstract)
2. `subgaussian_tail_bound`
3. `subgaussian_moment_growth`
4. `subgaussian_linear_combination`
5. `subgaussian_centering`
6. `subgaussian_sum_bound` (useful for Hoeffding style derivations)

Each with Vershynin citations.

#### 12.3 `Subexponential.lean`

Axioms:

* definition function `subexponential_norm`
* tail bound
* closure under sums
* relationship between subgaussian squared and subexponential (optional)

Citations: Vershynin or Wainwright.

#### 12.4 `Hoeffding.lean`

Axioms:

* bounded independent variables tail inequality for sums
* version for bounded differences if desired (or keep in Azuma)
* simple corollary forms used in ML

Citations: standard texts (Vershynin, Boucheron-Lugosi-Massart, etc).

#### 12.5 `Bernstein.lean`

Axioms:

* scalar Bernstein inequality with variance term
* simplified corollary form

Citations: Vershynin or Wainwright.

#### 12.6 `Azuma.lean` and `Freedman.lean`

Axioms:

* Azuma Hoeffding for martingales
* Freedman inequality for bounded increments with variance process

Citations: standard probability references.

#### 12.7 `MatrixBernstein.lean`

Axioms:

* matrix Bernstein tail bound for sum of independent random self adjoint matrices
* operator norm bound form

Citations: Tropp.

#### 12.8 `MatrixHoeffding.lean`

Axioms:

* matrix Hoeffding for bounded matrices

Citations: Tropp or other.

#### 12.9 `GaussianSpectralNorm.lean`

Axioms:

* bound on spectral norm of Gaussian random matrix
* high probability form and expectation form (optional)

Citations: Vershynin, Tropp, or standard RMT text.

---

### 13. Index and mapping layer specification

This is essential for trust and adoption.

#### 13.1 `index/sources/*`

One file per source, contains:

* full bibliographic citation
* scope of results used
* mapping list: theorem numbers to Lean axiom identifiers

Example `index/sources/vershynin_hdp.md`:

* citation
* chapter list
* table: “Theorem 2.1.1 -> subgaussian_tail_bound”

#### 13.2 `index/map/*`

One file per topic area:

* enumerates Lean modules
* lists axioms, grouped by concept
* links to sources

Example `index/map/probability_concentration.md` includes:

* Scalar
* Martingale
* Matrix

#### 13.3 `index/load_bearing_axioms.md`

A curated short list of axioms that many downstream results will depend on.

* used to communicate risk and priorities
* used as targets for eventual formalization proposals

---

### 14. Migration and deprecation policy

#### 14.1 Goals

* When mathlib proves a theorem, Scaffold should be able to replace the axiom with a reexport without breaking downstream code.

#### 14.2 Mechanism

When mathlib provides `Mathlib.X.Y.Z` with the same name and statement, do:

1. Replace axiom with:

   * an import of the mathlib file
   * a `theorem` alias if needed
2. Mark the old axiom name as deprecated if a rename is required.

Preferred approach is to keep the exact identifier so downstream code does not change.

#### 14.3 Deprecation rules

* Deprecate for at least one minor release before removal.
* Provide a migration note in `governance/RELEASES.md`.

---

### 15. Versioning

Use semantic versioning:

* `0.y.z` while stabilizing API
* `1.0.0` once the namespace structure and core modules are stable

Release cadence:

* monthly or quarterly
* always pin a mathlib version and record it in release notes

---

### 16. Licensing

Choose a permissive license to maximize adoption.

Recommended:

* **Apache 2.0** (excellent for corporate use, patent friendly language)
* or **MIT** (simple, very permissive)

If your priority is broad industry adoption, Apache 2.0 is a strong default.

---

### 17. Contribution workflow

#### 17.1 PR types

1. **Axiom addition**

   * adds axioms with citations and index updates
2. **Index improvement**

   * improves mapping quality, bibliographic details
3. **API cleanup**

   * refactors modules without breaking changes
4. **Migration PR**

   * replaces axioms with mathlib reexports

#### 17.2 Required checks for axiom PRs

Axiom PR must include:

* Lean axiom(s) with doc comment and citation
* `index/sources/<source>.md` update
* `index/map/<area>.md` update

Optional:

* a small “intent test” file demonstrating typical usage

#### 17.3 Review checklist

Maintainers verify:

* statement is faithful and not overstated
* hypotheses are explicit and minimal
* citation is precise
* names match mathlib style
* no new sorry leaked into public API

---

### 18. Guardrails to prevent abuse

Add a CI or lint rule:

* forbid the token `sorry` outside `Scaffold/Trusted/**`
* forbid `axiom` outside `Scaffold/Mathlib/**` unless explicitly permitted
* optionally enforce citation template presence for any new axiom

---

### 19. Templates

#### 19.1 Axiom request issue template

Fields:

* topic area
* source reference
* theorem statement (informal)
* suggested Lean statement
* why it matters and likely downstream uses

#### 19.2 New module template

Every new module must include:

* scope doc at top
* sources list
* list of axioms provided
* what is intentionally excluded

---

### 20. Minimal umbrella imports

`Scaffold.lean` should be small and safe:

* either empty
* or only reexport a few high level modules

Avoid making `import Scaffold` pull in half the world, that hurts compile times.

---

### 21. Roadmap

Phase 1, adoption magnet:

* scalar concentration
* martingale concentration
* matrix concentration
* gaussian spectral norm

Phase 2, expansion:

* random graphs and spectral gaps
* perturbation theory modules

Phase 3, convergence:

* propose a pipeline for migrating selected axioms into mathlib
* maintain a list of “formalization bounties” in issues

---

### 22. Suggested positioning text for README

Short blurb:

> Scaffold is a mathlib compatible Lean layer that treats trusted textbook results as explicit axioms so developers can build formally checked new reasoning today. Each axiom is precisely cited and designed to be replaced by fully proved mathlib theorems over time.

---

### 23. Concrete initial deliverables checklist

For your coding agent to generate the repo, start with these files:

1. `LICENSE`
2. `README.md`
3. `lakefile.lean` and `Scaffold.lean`
4. `governance/AXIOM_POLICY.md` and `DEPRECATION_POLICY.md`
5. `Scaffold/Mathlib/Core/RandomVariable.lean`
6. `Scaffold/Mathlib/Probability/Concentration/Scalar/Subgaussian.lean`
7. `Scaffold/Mathlib/Probability/Concentration/Scalar/Hoeffding.lean`
8. `Scaffold/Mathlib/Probability/Concentration/Scalar/Bernstein.lean`
9. `index/sources/vershynin_hdp.md`
10. `index/sources/tropp_tail_bounds.md`
11. `index/map/probability_concentration.md`
12. `.github/workflows/ci.yml` with build and guardrails

That is enough to publish a credible v0.1 that people can use immediately.

---

### 24. Optional: “mathlib compatibility contract”

Add a short policy document stating:

* Scaffold will prefer mathlib’s definitions and types.
* Scaffold will mirror mathlib’s folder and namespace naming.
* Scaffold will align theorem names with mathlib conventions even before mathlib contains them.
* Scaffold will replace axioms with mathlib theorems whenever possible, with minimal disruption.

This single document helps prevent the project drifting into a fork.

---

If you want, I can also provide the exact contents for:

* `lakefile.lean`
* `ci.yml` guardrails
* `AXIOM_POLICY.md` and `DEPRECATION_POLICY.md`
* initial Lean files for Subgaussian, Hoeffding, Bernstein, MatrixBernstein with citation blocks and placeholders that compile against mathlib types
