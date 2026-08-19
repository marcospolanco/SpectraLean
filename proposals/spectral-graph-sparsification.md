# Proposal: Foster's Theorem, and (Separately, Blocked) Spielman–Srivastava Sparsification

**Status:** Split 2026-08-18 into two independently-gated pieces on review —
see "Correction" below before treating this as one proposal. **Phase A
(Foster's theorem): priority High, ready now.** **Phase B (the
sparsification guarantee): not ready — blocked on a factual error in its
own citation, requires a scope decision before any Lean work.** This
document authorizes no Lean changes, axiom admissions, commits, clean-room
copying, or external publication on its own.

## Correction (2026-08-18, on review)

Two findings, both load-bearing on whether this proposal can proceed as
originally written.

**Phase 4's citation does not exist.** The original text applies
`Scaffold.Probability.Concentration.MatrixChernoff.matrix_chernoff_upper_lower`
as though it were an already-proved theorem sitting on the shelf. It is
not — there is no `MatrixChernoff.lean` anywhere in this repository
(confirmed by direct search); `Concentration/Matrix/` contains only
`Hoeffding.lean`, `Bernstein.lean`, and `Azuma.lean`. The nearest candidate,
`matrix_bernstein`, is itself an **admitted axiom**, not a proved bound, and
matrix Bernstein and matrix Chernoff are related but distinct theorems —
whether `matrix_bernstein`'s exact hypotheses can actually supply what
Phase 4 needs is unsurveyed, not merely uncited. This is not a citation
typo to patch; the entire sparsification *guarantee* (the actual headline
result) currently rests on nothing. See Phase B below for what this means
for scope.

**Foster's theorem was explicitly removed from the program once already.**
`electrical-structure-crust.md`'s own "Deferred and removed" section states
plainly: "Foster's theorem — removed from the program... needs a rank/trace
identity of pseudoinverse character... re-admit only as its own proposal,
with a dependency path." This document re-admits it as its own proposal
(satisfying the letter of that instruction) but its own proof sketch
invokes exactly the pseudoinverse route that was rejected —
`Tr(L^{1/2}L^+L^{1/2})` — without acknowledging or reconciling with the
prior decision. There is, however, a genuine alternative that was not
available when Foster got rejected: an eigenbasis-only proof, reusing
exactly the machinery the Courant–Fischer engine and its consumers proved
today. Express `effectiveResistance A u v` via the eigenbasis expansion of
the potential solving the unit-demand equation (the same construction
`exists_laplacian_mulVec_eq_of_sum_eq_zero` already builds); swap the
summation order in `∑ A i j · R i j`; use `quadForm(L, v_k) = λ_k‖v_k‖²`
for each eigenvector; and use the now-proved fact
(`laplacian_kernel_eq_span_onesVec`) that the kernel is exactly
one-dimensional for a connected graph — every one of the `n−1` nonzero
eigenvalues then contributes exactly `1` to the sum, term by term, giving
`n − 1` directly. No `L^+`, no matrix square root, no new Mathlib
machinery — only algebra already proved. This route is why Phase A below
is scoped as ready despite the prior removal, not a quiet reversal of that
decision.

Companion to [Strategy](../docs/1_STRATEGY.md), [Traction Plan](../docs/traction-plan.md), [SGT Backlog](../docs/6_SGT_BACKLOG.md), [SGT Radar](../docs/7_SGT_RADAR.md) axes 6 (Electrical) & 7 (Algorithms/Randomness), and (companion to Phase A only — see Correction above) [Grow the Crust Through Electrical Structure](electrical-structure-crust.md), whose "Foster's theorem — removed" decision this proposal's Phase A reopens with a named reason. `Scaffold/Mathlib/Probability/Concentration/MatrixChernoff.lean` does not exist; do not treat it as a citable dependency for Phase B.

---

## Clean-room boundary

This planning document is internal prioritization and mathematical specification. If counsel approves a public repository export, restate the technical definitions and proof sequence independently from standard literature sources (Spielman–Srivastava 2011, Tropp 2012). Do not copy this proposal verbatim or consult quarantined materials.

---

## The Intellectual Thesis

In 2008, Daniel Spielman and Nikhil Srivastava published a landmark breakthrough in theoretical computer science and spectral graph theory: **every dense graph $G = (V, E, w)$ on $n$ vertices contains an ultra-sparse spectral proxy $\tilde{G}$ with only $O(n \log n / \epsilon^2)$ edges that preserves every Laplacian quadratic form within a $(1 \pm \epsilon)$ multiplicative factor:**

$$(1 - \epsilon) x^T L_G x \le x^T L_{\tilde{G}} x \le (1 + \epsilon) x^T L_G x \quad \forall x \in \mathbb{R}^V$$

This guarantees that $\tilde{G}$ simultaneously preserves **all cut values**, **all Rayleigh quotients**, **all electrical effective resistances**, and **all random-walk diffusion rates** of the original graph up to $(1 \pm \epsilon)$, while discarding almost all edges.

The mathematical core of the proof relies on a surprising identity: **the optimal importance-sampling distribution for edge sparsification is given exactly by the electrical leverage scores $p_e \propto w_e R_{\mathrm{eff}}(e)$.**

---

## Why this moves [`docs/traction-plan.md`](../docs/traction-plan.md)

[`docs/traction-plan.md`](../docs/traction-plan.md#L30-L40) specifies that the library should lead with concrete, high-value integration theorems for Lean and Mathlib contributors:

1. **Would unify Scaffold's architecture, if Phase B ever lands:**
   Scaffold has the Zero-Axiom Electrical Crust (`GraphTheory.Electrical`)
   and a real matrix-concentration bridge (`Probability.Concentration.Matrix.{Hoeffding,Bernstein,Azuma}`
   — admitted axioms, not `MatrixChernoff`, which does not exist). Spectral
   sparsification would be the theorem connecting them, but that connection
   is not currently available; see "Correction" above.
2. **First Formalized Sparsifier — aspirational, not current.**
   No interactive theorem prover has a certified spectral graph
   sparsification theorem yet. This proposal's Phase B, if a real matrix
   concentration route is ever scoped, is a candidate to be first — but is
   not close to that today.
3. **Foster's Theorem as Hard Crust — this part is real and ready now.**
   Foster's Theorem ($\sum_{e} w_e R_e = n - 1$) is provable as a 100%
   hard-crust theorem with zero axioms, via the eigenbasis route in
   "Correction" above — not the pseudoinverse trace identity the original
   text described.

---

## Technical Overview & Formal Architecture

## Phase A: Foster's Theorem — ready now, priority High

### Elementary Edge Laplacians & Foster's Theorem (`GraphTheory.Foster`)

For an undirected edge $e = (u, v)$ with conductance $w_e$:
* The elementary edge Laplacian is $L_e = w_e (e_u - e_v)(e_u - e_v)^T$.
* Proved decomposition: $L = \sum_{u < v} L_{uv}$.
* The electrical resistance $R_{\mathrm{eff}}(u, v) = (e_u - e_v)^T L^+ (e_u - e_v)$.
* **Foster's Theorem:** In any connected graph on $n$ vertices with positive conductances:
  $$\sum_{u < v} A_{uv} R_{\mathrm{eff}}(u, v) = n - 1$$
  *Proof route (the classical $L^{1/2}L^+L^{1/2}$ trace identity is background
  motivation only — do not formalize it; see "Correction" above for why):*
  express `effectiveResistance A u v` via the eigenbasis expansion of the
  potential solving the unit-demand equation, swap the summation order in
  the double sum, apply `quadForm(L, v_k) = λ_k‖v_k‖²` per eigenvector, and
  use `laplacian_kernel_eq_span_onesVec` to know the kernel is exactly
  one-dimensional — each of the `n − 1` nonzero eigenvalues contributes
  exactly `1`. No pseudoinverse object is defined or consumed anywhere in
  this route.

## Phase B: The Sparsification Guarantee — not ready, blocked

**Do not begin any Lean work on this phase.** It depends on a theorem
(Phase 4, below) that does not exist in this repository under any name.
Before this phase can be scoped as a real proposal, someone needs to
decide — and this document does not decide it — whether to (a) survey
whether the existing `matrix_bernstein` axiom's exact hypotheses can
actually supply what Phase 4 needs, (b) admit a new, carefully-scoped
matrix-Chernoff-shaped axiom with its own citation and center-out
leverage case (the `admit-perron-frobenius.md` pattern), or (c) attempt a
from-scratch proof, which would very likely need machinery on the order
of Lieb's concavity theorem or the Golden–Thompson inequality — nothing
resembling either exists in the pinned Mathlib. Any of the three is a
real, separate proposal's worth of scoping, not a Lean-implementation
detail to discover mid-run. `sampledLaplacian` in the Lean sketch below is
also undefined anywhere in this repository — a second placeholder, not
yet a real declaration.

The full technical analysis of why (the exact point the scalar Chernoff
proof breaks for non-commuting matrices, what Golden–Thompson/Lieb's
theorem actually require, and the verified Mathlib search) is kept
separately, not duplicated here, in
[`icebox/matrix-chernoff-formalization-gap.md`](../icebox/matrix-chernoff-formalization-gap.md) —
general enough to outlive this specific proposal.

### Resistance Leverage Scores & Random Edge Sampler

Define the probability distribution on unordered pairs:
$$p_{uv} = \frac{A_{uv} R_{\mathrm{eff}}(u, v)}{n - 1}$$
By Foster's Theorem, $\sum_{u < v} p_{uv} = 1$, making $p$ a valid probability measure on edges.

For a target sample size $M$, independently sample edges $e_1, \dots, e_M \sim p$ and assign the re-weighted conductance:
$$\tilde{w}_e = \frac{w_e}{M p_e} = \frac{n - 1}{M R_{\mathrm{eff}}(e)}$$

### The Whitened Edge Operators & Spectral Norm Bound

In the subspace $\mathbf{1}^\perp$, define the normalized random matrix $Y_k = \frac{1}{M p_{e_k}} L^{1/2+} L_{e_k} L^{1/2+}$.
1. **Unbiased Expectation:** $\mathbb{E}[Y_k] = \frac{1}{M} I_{\mathbf{1}^\perp}$.
2. **Spectral Norm Bound:**
   $$\|Y_k\|_2 = \frac{1}{M p_e} \|L^{1/2+} (e_u - e_v)\|_2^2 = \frac{w_e R_e}{M p_e} = \frac{n - 1}{M}$$
   The effective resistance in the denominator exactly cancels the vector norm, rendering every sampled edge operator bounded by $\frac{n-1}{M}$!

### The Sparsification Guarantee (blocked — see "Correction" above)

The step below is what does not exist yet. Applying
`Scaffold.Probability.Concentration.MatrixChernoff.matrix_chernoff_upper_lower`
(this declaration does not exist — see above):
$$\mathbb{P}\left[ (1 - \epsilon) L \preceq \tilde{L} \preceq (1 + \epsilon) L \right] \ge 1 - 2n \exp\left( - \frac{\epsilon^2 M}{3 (n - 1)} \right)$$

Choosing $M = \lceil \frac{3 (n - 1) \ln(2n / \delta)}{\epsilon^2} \rceil$ yields a certified $(1 \pm \epsilon)$-spectral sparsifier with probability at least $1 - \delta$.

---

## Lean Interface Sketch

### Phase A (ready)

```lean
namespace Scaffold.GraphTheory.Foster

open Scaffold.GraphTheory.Spectral
open Scaffold.GraphTheory.Electrical

/-- The leverage score probability of an edge in a connected weighted graph. -/
def leverageScore (A : Matrix V V ℝ) (u v : V) : ℝ :=
  (A u v * effectiveResistance A u v) / (Fintype.card V - 1)

/-- Foster's Theorem: total leverage score sums to n - 1 (proved hard crust,
    eigenbasis route only — see "Correction" above). -/
theorem foster_theorem
    (A : Matrix V V ℝ) (hA_sym : A.IsSymm) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (h_conn : (supportGraph A hA_sym).Connected)
    (hcard : 2 ≤ Fintype.card V) :
    (∑ i, ∑ j, A i j * effectiveResistance A i j) / 2 = Fintype.card V - 1
```

### Phase B (blocked — sketch only, do not implement)

```lean
-- Requires a matrix-Chernoff-shaped result this repository does not have,
-- and `sampledLaplacian`, which is not defined anywhere. Not ready.
theorem spielman_srivastava_sparsification
    (A : Matrix V V ℝ) (hA_sym : A.IsSymm) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (h_conn : (supportGraph A hA_sym).Connected)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (M : ℕ) (hM : (3 * (Fintype.card V - 1) * Real.log (2 * Fintype.card V / δ) / ε^2) ≤ M) :
    ∃ (μ : Measure (Fin M → V × V)),
      μ { edges | ∀ x, (1 - ε) * quadForm (laplacian A) x ≤
                         quadForm (sampledLaplacian A edges M) x ∧
                         quadForm (sampledLaplacian A edges M) x ≤
                         (1 + ε) * quadForm (laplacian A) x } ≥ 1 - δ
```

---

## Calibration and Sharp Edges

**Phase A:**

3. **Double Counting Factor:**
   Symmetric matrices sum over all pairs $(u, v)$, so the undirected edge sum carries a factor of $1/2$. QA must explicitly test this factor on small cliques ($K_3, K_4$).

**Phase B (moot until the blocker above is resolved, kept for whoever eventually scopes it):**

1. **Subspace Restrictions ($\mathbf{1}^\perp$):**
   The Laplacian $L$ is singular, so the Loewner ordering $(1-\epsilon) L \preceq \tilde{L} \preceq (1+\epsilon) L$ holds on the entire space $\mathbb{R}^V$ because both $L$ and $\tilde{L}$ have $\mathbf{1}$ in their nullspace. The matrix Chernoff bound must be applied on the $(n-1)$-dimensional subspace $\mathbf{1}^\perp$.
2. **Zero-Weight / Non-Edge Handling:**
   Pairs with $A_{uv} = 0$ have leverage score $0$ and must be excluded from sampling to prevent division by zero.

---

## Public Scientific Anchors

* **[SS]** Daniel A. Spielman and Nikhil Srivastava, *"Graph Sparsification by Effective Resistances,"* SIAM Journal on Computing 40 (2011), 1913–1926. (Phase B.)
* **[F]** Ronald M. Foster, *"The Average Impedance of an Electrical Network,"* Contributions to Applied Mechanics (Reissner Anniversary Volume), Edwards Brothers, 1949, 333–340. (Phase A.)
* **[T]** Joel A. Tropp, *"User-Friendly Tail Bounds for Matrix Martingales,"* Foundations of Computational Mathematics 12 (2012), 389–434. (Phase B — and note this is a general tail-bound survey, not itself the matrix Chernoff bound Phase B's proof sketch names; confirm it actually contains a directly-applicable statement before citing it as the route.)

---

## Operating instructions for an autonomous run

- **Phase A only.** Do not begin any Phase B work — not the leverage-score
  sampler, not the whitened operators, not the sparsification statement —
  under this proposal. Phase B needs its own scoping proposal once the
  matrix-Chernoff blocker in "Correction" is resolved one of the three ways
  named there.
- One step per run: `foster_theorem` and its QA is sized to land in one run;
  if the eigenbasis-summation-swap argument turns out to need its own
  reusable lemma, that may span two.
- No new axioms. If the eigenbasis route hits a genuine gap, record the
  exact obstruction rather than falling back to the pseudoinverse route the
  prior proposal already rejected.
- Survey Mathlib before proving, per standing convention.

## Acceptance Criteria

**Phase A:**

1. **Foster's Theorem proved:** Full hard-crust proof of $\sum_{u < v} w_e R_e = n - 1$ in `GraphTheory.Foster` with zero new axioms, via the eigenbasis route only.
3. **Comprehensive QA:** `SpectralGraph/Foster_QA.lean` calculating exact leverage scores on complete graphs ($R_e = 2/n$, total sum $n-1$), paths, and stars.
4. **Docs updated:** Index maps, scoreboard, and radar reflecting Phase A only.

**Phase B (not applicable until scoped as its own proposal):**

2. **Sound reduction:** The sparsification theorem derived cleanly by applying a real, surveyed or newly-scoped matrix concentration result to the normalized edge operators — not `MatrixChernoff`, which does not exist.
