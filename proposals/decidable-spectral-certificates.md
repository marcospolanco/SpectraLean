# Proposal: Decidable Spectral Certificates and the Expander Mixing Lemma

**Status:** Proposed; **priority:** High (upgraded 2026-08-18 from Medium,
contingent on the Step 0 survey below landing before Step 1 begins). Proposed
2026-08-18 to bridge continuous spectral theory with combinatorial
pseudorandomness and close the noncomputable extraction gap identified in
`docs/traction-plan.md`. This document authorizes no Lean changes, axiom
admissions, commits, clean-room copying, or external publication on its own.
**Step 0 is COMPLETE (2026-08-19)** — see the decision record in the build
order below; Steps 1+ are unblocked.

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
4. **Adjacency vs. Laplacian eigenvalue convention — RESOLVED 2026-08-19
   (Step 0, Decision 1): Laplacian-first through the `d`-regular bridge**
   `μ = max(|d − λ₂(L)|, |d − λ_max(L)|)`. See the Step 0 record for the
   survey evidence and the restated theorem signature.
5. **`decide` on ℚ arithmetic is an unverified performance risk — RESOLVED
   2026-08-19 (Step 0, Decision 2): it is not merely slow, it does not
   kernel-reduce at all** (`Rat` operations are opaque to elaborator
   reduction in the pinned environment). The kernel-verifiable checker is
   the integer cross-multiplied twin; see the Step 0 record.

---

## Public Scientific Anchors

* **[AC]** Noga Alon and Fan R. K. Chung, *"Explicit construction of linear sized tolerant networks,"* Discrete Mathematics 72 (1988), 15–19. (Original Expander Mixing Lemma).
* **[HLW]** Shlomo Hoory, Nathan Linial, and Avi Wigderson, *"Expander graphs and their applications,"* Bulletin of the AMS 43 (2006), 439–561.
* **[V]** Salil Vadhan, *"Pseudorandomness,"* Foundations and Trends in Theoretical Computer Science 7 (2012), 1–336.

---

## Proposed Build Order

### Step 0: Survey and resolve the two open gaps

**STATUS: COMPLETE (2026-08-19).** All three items below are decided and
recorded here, per this section's own instruction, before any Step 1 code.
The spike artifacts were scratch files (not committed, not part of any
build target); the decisive commands and outcomes are recorded below.

#### Decision 1 — Convention: Laplacian-first, through the d-regular bridge

`expander_mixing_lemma` is stated with its spectral hypothesis in
**Laplacian** terms. Survey evidence (2026-08-19, this repository):

- No adjacency-*eigenvalue* interface exists anywhere in the codebase.
  `grep` over `Scaffold/` shows adjacency only as weight matrices and QA
  fixtures; every spectral declaration (`evals`, `lambda2`, `lambda2`,
  `lambda2_variational`, `secondEval`, `secondEval_le_rayleigh`, the
  Courant–Fischer engine, all `eigvecOf` machinery) is either
  Laplacian-wrapped or generic-symmetric.
- The certificate half of this proposal (Step 3) is already Laplacian
  (`lambda2 (laplacian A)`); a common convention keeps the EML and the
  certificates composable — a verified bound `λ₂(L) ≤ d − μ` is exactly
  the input the bridged EML consumes.
- The generic symmetric-matrix engine applies to an adjacency matrix for
  free (it only needs `IsSymm`), so proving the bridge needs **no new
  adjacency-spectral interface**: under loopless `d`-regular weights,
  `A = d • 1 − L` entrywise, adjacency and Laplacian eigenvectors
  coincide, and adjacency eigenvalues are `d − λᵢ(L)`. The only new cost
  is the affine spectrum transfer plus a Rayleigh-form bound on `1⊥`,
  both Step 2 work.
- No named consumer requires adjacency eigenvalues.

**Restated theorem signature** (replacing the convention-free draft;
`edgeWeight` is Step 1's definition; the `√`-form is the mathematical
statement — the Lean-facing form may square both sides to stay in
ordered-field arithmetic, a Step-2 implementation choice, since both
sides are nonnegative):

```lean
theorem expander_mixing_lemma
    (A : WAdj (V := V)) (hsymm : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hloop : ∀ i, A i i = 0) (d : ℝ) (hreg : ∀ i, deg A i = d)
    (hcard : 2 ≤ Fintype.card V) (μ : ℝ)
    (hμ : max |d - lambda2 A hsymm hcard|
          |d - evals (laplacian_symmetric A hsymm)
              ⟨Fintype.card V - 1, by omega⟩| ≤ μ)
    (S T : Finset V) :
    |edgeWeight A S T - d * (S.card : ℝ) * (T.card : ℝ) / Fintype.card V| ≤
      μ * √(S.card * T.card * (Fintype.card V - S.card)
              * (Fintype.card V - T.card)) / Fintype.card V
```

The proof layers stay as the build order sketches: (a) the pure
linear-algebra core (the indicator decomposition is convention-free, so
Step 1 is unblocked by this decision), (b) the bridge from the eigenvalue
hypothesis to the Rayleigh-form operator bound on `x ⊥ 1`, (c) the
packaged corollary above.

#### Decision 2 — `decide` spike: ℚ arithmetic as sketched is NOT
kernel-decidable; the integer cross-multiplied twin IS

Plain kernel `decide` **cannot** verify the Step-3 checker as drafted —
this is a reducibility wall, not a performance limit. Evidence (scratch
elaboration against the pinned environment, `lake env lean`):

- `(0 : ℚ) < 2` decides (literal comparison only), but `((2:ℚ) + 2) = 4`
  is already stuck: elaborator reduction halts at `(Rat.add 2 2).num` —
  ℚ literals are opaque kernel literals, `Rat.add`'s matcher cannot fire,
  and elaborator `whnf` has no `Rat`-operation acceleration. Every
  nontrivial ℚ computation (sums `/`, `≤` via `Rat.blt`, `==` via
  `Rat.decEq`) fails the same way (`∑ i : Fin 4, v i = 0` on
  `v = ![1,0,-1,0]` sticks at an unapplied `Rat.add`).
- `#eval` of the same checker returns `true` (native extern code), but
  that is not kernel-checked and `native_decide` is excluded by this
  proposal's own trust-posture rule. Not a fallback.
- Control probes that *do* decide: `Nat.gcd 6 4 = 2`, `∑ i : Fin 4, (i:ℕ) = 6`,
  `(2:ℤ) * 3 - 5 = 1` — the obstruction is specific to `Rat` operations.

**Adopted fallback (recorded per this section's own instruction):** the
kernel-verifiable checker is the **integer cross-multiplied twin** — all
certificate data integer (adjacency entries, test vector with
denominators cleared, rational bound as an integer numerator/denominator
pair), and the rational inequality replaced by its cross-multiplied
integer form:

```lean
def isSpectralUpperBoundCertificateInt {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) (bound : ℤ) : Bool :=
  let dotOne := ∑ i, v i
  let denom := ∑ i, (v i)^2
  let rawNumer := ∑ i, ∑ j, (A i j) * (v i - v j)^2
  (dotOne == 0) && decide (0 < denom) && decide (rawNumer ≤ 2 * bound * denom)
```

(`rawNumer/(2 · denom) ≤ bound` with `denom > 0`; a fractional bound
`num/boundDen` is `boundDen * rawNumer ≤ 2 * num * denom`.) Verified by
kernel `decide`, accept and reject paths, at both required sizes: `C₄`
(`Fin 4`, certificate `![1,0,-1,0]` attaining `λ₂ = 2`: accepted at
bound `2`, rejected at `1`; non-orthogonal and zero test vectors
rejected) and `C₆` (`Fin 6`, `![1,1,0,-1,-1,0]` attaining `λ₂ = 1`:
accepted at `1`, rejected at `0`); fractional form on `C₄`: `λ₂ ≤ 5/2`
accepted, `λ₂ ≤ 3/2` rejected. Decisive commands: `lake env lean` on
the probe files — failures exactly as described for ℚ; the
integer-twin acceptance file elaborates clean in ~15 s wall (almost all
`Mathlib.Tactic` import; per-`decide` overhead well under a second).
Step 3 therefore delivers **both** the ℚ-facing soundness statement and
this ℤ twin, bridged by a proved lemma (cross-multiplication in ordered
fields — pure algebra, no `decide`); Acceptance Criterion 2 is read
against the ℤ twin.

#### Decision 3 — Ramanujan QA scope: use the existing fixture family; no external sourcing

"Ramanujan graph examples" in Step 4 means: the fixtures already in the
QA family — cycles `Cₙ` (`d = 2`, adjacency spectrum `2cos(2πk/n)`,
published standard) and complete graphs `Kₙ` (`d = n−1`, μ = 1) — are
themselves small Ramanujan instances for `n ≥ 3` (`μ(C₄) = 2 = 2√(d−1)`
with equality; `μ(C₆) = 1 ≤ 2`; `μ(K₃) = 1 ≤ 2`). Checking
Ramanujan-ness reduces to the same pinned-spectrum computations Step 2's
bridge needs anyway. No construction, no family proof, no external
sourcing; if the spectral-bound check proves awkward once Step 4 is
reached, drop the label rather than expand scope, per this section's
own fallback.

### Step 1: Combinatorial Edge Weight and Discrepancy Core
Define subset edge weight:
```lean
def edgeWeight (A : Matrix V V ℝ) (S T : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, A i j
```
Prove decomposition of characteristic vectors $\mathbf{1}_S = \alpha \mathbf{1} + v_S^\perp$ where $v_S^\perp \perp \mathbf{1}$.

**STATUS: DELIVERED (2026-08-19)** as `Scaffold.Mathlib.GraphTheory.Expander`
(pure hard crust, zero new axioms; `#print axioms` on every public
theorem reads only `propext, Classical.choice, Quot.sound`):

- `edgeWeight` exactly as sketched, with degenerate-cut guards, the
  degree-sum form `edgeWeight A S univ = ∑ i ∈ S, deg A i`, the
  hypothesis-free matrix form `edgeWeight_eq_dotProduct`
  (`indicatorVec S ⬝ᵥ (A *ᵥ indicatorVec T)` — the bilinear identity
  Step 2's spectral proof starts from), and `edgeWeight_symm` (sum
  swap under entrywise symmetry).
- `indicatorVec` / `centeredIndicator` with the decomposition
  `indicatorVec_eq_smul_onesVec_add_centeredIndicator` and
  `sum_centeredIndicator_eq_zero` /
  `centeredIndicator_dotProduct_onesVec` — the orthogonality is
  **unconditional** (the empty-type case is handled; no `Nonempty`
  hypothesis carried), a small statement-shape strengthening over the
  sketch.
- The headline `edgeWeight_eq_regular_add_centered`:
  `edgeWeight A S T = d · |S| · |T| / |V| + centeredIndicator S ⬝ᵥ (A
  *ᵥ centeredIndicator T)` on symmetric `d`-regular networks. Both
  hypotheses are load-bearing: symmetry through
  `Matrix.dotProduct_mulVec`'s transpose (the `1 ⬝ᵥ (A *ᵥ v)` cross
  term dies only after `Aᵀ = A`), regularity through
  `mulVec_onesVec_eq_const` (`A *ᵥ onesVec = d`, consuming `deg`'s
  row-sum shape).

QA `Scaffold/QA/SpectralGraph/Expander_QA.lean` (22 declarations, fresh
`C₄` fixture per the QA-independence convention): all values computed
from the raw definitions — adjacent cut `1`, opposite cut `0`,
half-and-half `2`, total `8`, matrix form cross-checked, centered
indicators pinned entrywise (`±1/2`, `3/4/−1/4`) with orthogonality
computed from the pinned entries; the decomposition instantiated on an
adjacent cut (`1 = 1/2 + 1/2`) and an opposite cut (`0 = 1/2 − 1/2`),
cross terms computed independently; three negative witnesses — the
main-term-only statement refuted on the opposite cut (`0 ≠ 1/2`), the
main term's degree pinned by regularity (wrong `d = 3` refuted,
`1 ≠ 3/4`), and cut-weight symmetry genuinely failing on the
asymmetric weight `!![0,2;1,0]` (`2 ≠ 1`).

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
