# Proposal: Decidable Spectral Certificates and the Expander Mixing Lemma

**Status:** Proposed; **priority:** High (upgraded 2026-08-18 from Medium,
contingent on the Step 0 survey below landing before Step 1 begins). Proposed
2026-08-18 to bridge continuous spectral theory with combinatorial
pseudorandomness and close the noncomputable extraction gap identified in
`docs/traction-plan.md`. This document authorizes no Lean changes, axiom
admissions, commits, clean-room copying, or external publication on its own.

**Why High, and why contingent.** The certificate-soundness argument is a
genuine, checked-by-hand load-bearing consumer of `lambda2_variational`
(proved, not admitted, delivered the same day this proposal was written): the
certificate's `numer` term is exactly `quadForm (laplacian A) v`
(`laplacian_quadForm`'s identity), so `numer/denom` is `rayleigh (laplacian A) v`,
and `dotOne = 0` places `v` directly in the constraint set
`lambda2_variational` already characterizes — `lambda2 = sInf S ≤ rayleigh(v)
≤ bound` falls out in a few lines, not a hand-wave. This closes the exact
extraction gap `docs/traction-plan.md` names as the reason broader-audience
outreach stays premature, which makes it strategically bigger than a typical
proof target. The contingency is two real, currently unaddressed gaps — see
Step 0.

Companion to [Strategy](../docs/1_STRATEGY.md), [Traction Plan](../docs/traction-plan.md), [SGT Backlog](../docs/6_SGT_BACKLOG.md) item 3/4, and [SGT Radar](../docs/7_SGT_RADAR.md) axes 4 (Cuts/Expansion) & 7 (Algorithms).

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If counsel approves a public repository export, restate the technical specifications independently from standard textbook sources on expander graphs and certificate checking. Do not copy this proposal verbatim or consult quarantined materials.

---

## The Strategic Problem

[`docs/traction-plan.md`](../docs/traction-plan.md#L37-L46) explicitly recorded why broad engineering outreach (ML engineers, distributed systems developers) was premature:

> *"every proved result here is `noncomputable` Lean with no extraction path to a runnable artifact, so an engineer outside a proof assistant has nothing to consume yet. Revisit only if that extraction gap closes."*

Because Scaffold's spectral theory relies on classical choice (`Classical.choose`) and the real spectral theorem, eigenvalues $\lambda_k$ and eigenvectors $v_k$ cannot be evaluated by Lean's code generator or `#eval`. An outside practitioner running graph algorithms in Python, C++, or Rust cannot directly feed a large network into Lean and compute a certificate.

This proposal closes that exact extraction gap by introducing **proof-carrying spectral certificates** and pairing them with the classical **Expander Mixing Lemma**.

---

## Recommendation

Deliver two interlocking zero-axiom modules:

1. **The Expander Mixing Lemma (`GraphTheory.Expander`):**
   Prove that for any $d$-regular graph with second adjacency eigenvalue $\mu = \max(|\mu_2|, |\mu_n|)$, the number of edges $e(S, T)$ between any subsets $S, T \subseteq V$ satisfies the combinatorial discrepancy bound:
   $$\left| e(S, T) - \frac{d |S| |T|}{n} \right| \le \mu \sqrt{|S| |T| \left(1 - \frac{|S|}{n}\right)\left(1 - \frac{|T|}{n}\right)}$$
   This formalizes the foundational bridge between algebraic spectral gaps and combinatorial pseudorandomness.

2. **Decidable Rational Spectral Certificates (`GraphTheory.SpectralCertificates`):**
   Formalize a computable certificate verification layer over $\mathbb{Q}$.
   * **Upper bound certificate:** An external numerical solver (e.g. Lanczos/SciPy in float/rational) emits an inexact orthogonal test vector $\tilde{v} \in \mathbb{Q}^V$. Lean checks $\tilde{v} \perp \mathbf{1}$ and $\frac{\tilde{v}^T L \tilde{v}}{\tilde{v}^T \tilde{v}} \le \alpha$ entirely in rational arithmetic via `decide`. The proved theorem lifts this to a verified bound $\lambda_2(L) \le \alpha$ in $\mathbb{R}$.
   * **Bipartition certificate:** A rational sign vector certifies an explicit cut with certified conductance and edge discrepancy.

---

## Why this moves the intellect and the traction plan

* **Intellectual depth:** Unifies orthogonal spectral projection, Rayleigh minimization, and finite combinatorial measure. It connects continuous spectral geometry to discrete discrepancy theory.
* **Solves the extraction barrier:** Outside engineers do not need Lean to *find* the eigenvector; they use fast unverified numerical linear algebra to find a candidate, and Lean acts as the 100% verified, kernel-checked *certificate validator*.
* **Zero new axioms:** The Expander Mixing Lemma proves from Cauchy–Schwarz and the existing eigenbasis expansion (`Spectral.lean`). Certificate validation proves from the proved variational characterization (`lambda2_variational`) and ordered field homomorphisms $\mathbb{Q} \hookrightarrow \mathbb{R}$.
* **Upstream Mathlib appeal:** Mathlib has `Combinatorics.SimpleGraph` and basic walk definitions, but lacks expander graph theory and discrepancy bounds. This is a self-contained, high-prestige candidate for upstream PRs.

---

## Calibration and Sharp Edges

1. **Ordered Field Embedding ($\mathbb{Q} \hookrightarrow \mathbb{R}$):**
   Rational computations must lift faithfully to real matrices without re-elaborating costly proofs. The bridge `Matrix.map A (algebraMap ℚ ℝ)` must preserve symmetry and quadratic forms definitionally.
2. **Disconnected / Zero-Norm Protection:**
   A candidate witness with $v = 0$ or $v \not\perp \mathbf{1}$ must be rejected by the boolean decider. The certificate predicate must strictly check $\sum_i v_i = 0$ and $\sum_i v_i^2 > 0$ before dividing.
3. **Regular vs Irregular Normalization:**
   The standard Expander Mixing Lemma is stated for $d$-regular graphs. For general irregular graphs, the statement generalizes cleanly via the normalized Laplacian $L_{\text{sym}}$ and degree-weighted volumes $\mathrm{vol}(S), \mathrm{vol}(T)$. Scoping should begin with the regular case and extend via `VariationalTransfer`.
4. **Adjacency vs. Laplacian eigenvalue convention — unresolved as written.**
   The classical Expander Mixing Lemma bounds $\mu$, the second-largest
   *adjacency*-matrix eigenvalue. Every existing Scaffold spectral tool
   (`evals`, `lambda2`, `lambda2_variational`) is Laplacian-first; there is no
   adjacency-eigenvalue interface anywhere in this codebase. For $d$-regular
   graphs $\mu = d - \lambda_2(L)$ bridges the two, but Steps 1–2 as drafted
   work with a generic `Matrix V V ℝ` without saying which convention is
   meant or proving the bridge. Resolve this — pin one convention and prove
   the bridge identity if needed — before writing `expander_mixing_lemma`'s
   statement, not while proving it.
5. **`decide` on ℚ arithmetic is an unverified performance risk.**
   Acceptance Criterion 2 requires `decide` to kernel-verify certificate
   instances on concrete `Fin n` graphs. Lean 4's kernel has efficient
   GMP-backed `Nat`/`Int` reduction, so this is *probably* fine at small
   sizes — but "probably" is not sufficient for a criterion the traction
   story depends on, and `native_decide` (a different trust posture, not
   fully kernel-checked) is not an acceptable silent substitute if plain
   `decide` turns out to choke. Spike this on one concrete graph before
   committing to the full build order.

---

## Public Scientific Anchors

* **[AC]** Noga Alon and Fan R. K. Chung, *"Explicit construction of linear sized tolerant networks,"* Discrete Mathematics 72 (1988), 15–19. (Original Expander Mixing Lemma).
* **[HLW]** Shlomo Hoory, Nathan Linial, and Avi Wigderson, *"Expander graphs and their applications,"* Bulletin of the AMS 43 (2006), 439–561.
* **[V]** Salil Vadhan, *"Pseudorandomness,"* Foundations and Trends in Theoretical Computer Science 7 (2012), 1–336.

---

## Proposed Build Order

### Step 0: Survey and resolve the two open gaps

Before any Step 1 code lands, resolve both items 4–5 in "Calibration and
Sharp Edges" and record the decision:

- **Convention.** Decide whether `expander_mixing_lemma` is stated directly
  for the adjacency matrix (requiring a small new adjacency-eigenvalue
  interface, since none exists) or for the Laplacian via the $d$-regular
  bridge $\mu = d - \lambda_2(L)$ (reusing existing machinery, likely
  cheaper). Prefer the Laplacian route unless the survey finds a concrete
  reason the adjacency form is needed by a named consumer. Record the choice
  and restate the theorem signature in this proposal before Step 2 begins.
- **`decide` spike.** Construct one small concrete `Fin n` graph (`n` around
  4–6) with a known certificate, and confirm `decide` actually kernel-checks
  `isSpectralUpperBoundCertificate` on it in reasonable time. If it does not,
  record the exact failure and scope a fallback (e.g. restating the
  arithmetic to reduce kernel reduction cost) before treating Step 3 as
  ready — do not silently reach for `native_decide` as a substitute.
- **Ramanujan QA scope, clarified.** "Ramanujan graph examples" in Step 4
  means one small, concrete graph already known and independently verified
  to be Ramanujan (e.g. a documented small instance with published
  eigenvalues) — not a construction or a proof that some family is
  Ramanujan. If no suitable small instance is easy to source and verify,
  drop this specific QA item rather than let it expand the proposal's scope.

### Step 1: Combinatorial Edge Weight and Discrepancy Core
Define subset edge weight:
```lean
def edgeWeight (A : Matrix V V ℝ) (S T : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, A i j
```
Prove decomposition of characteristic vectors $\mathbf{1}_S = \alpha \mathbf{1} + v_S^\perp$ where $v_S^\perp \perp \mathbf{1}$.

### Step 2: Expander Mixing Lemma
Prove `expander_mixing_lemma` for regular graphs by expanding $\mathbf{1}_S^T A \mathbf{1}_T$ across the eigenspaces of $A$ and bounding the orthogonal component via Cauchy–Schwarz and $\mu$.

### Step 3: Computable Rational Certificate Validator
Define computable verification functions:
```lean
def isSpectralUpperBoundCertificate
    (A : Matrix V V ℚ) (v : V → ℚ) (bound : ℚ) : Bool :=
  let dotOne := ∑ i, v i
  let denom := ∑ i, (v i)^2
  let numer := ∑ i, ∑ j, (A i j) * (v i - v j)^2 / 2
  (dotOne == 0) && (denom > 0) && (numer ≤ bound * denom)
```
Prove the soundness theorem:
```lean
theorem lambda2_le_of_certificate
    (A : Matrix V V ℚ) (v : V → ℚ) (bound : ℚ)
    (h_cert : isSpectralUpperBoundCertificate A v bound = true) :
    lambda2 (Matrix.map A (algebraMap ℚ ℝ)) ≤ (bound : ℝ)
```

### Step 4: QA and Extraction Demonstration
* Implement `SpectralGraph/Expander_QA.lean` checking the Expander Mixing Lemma on the complete graph $K_n$, cycles $C_n$, and Ramanujan graph examples.
* Implement a concrete `#eval` / `decide` test verifying a rational certificate for a non-trivial graph.

---

## Acceptance Criteria

1. **Zero axioms:** All declarations in `GraphTheory.Expander` and `GraphTheory.SpectralCertificates` proved without `axiom` or `sorry`.
2. **Kernel decider:** `decide` successfully verifies certificate instances on concrete `Fin n` graphs.
3. **QA coverage:** Positive witnesses (attained bounds on small graphs) and negative witnesses (invalid certificates rejected by `decide`).
4. **Documentation:** Updated scoreboard, radar (axes 4 and 7), and traction plan notes.
