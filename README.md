# Scaffold

Scaffold is a growing, machine-checked formalization of spectral graph theory
in Lean 4. Every claim is exactly what it says: a proved theorem is proved by
the kernel, and every remaining assumption is a small, explicit, cited
placeholder for one specific unproven research result, never hidden behind
`sorry`. The library's job is to keep proving those placeholders away: the
explicit axiom count has already fallen from 10 to 4 as the hard crust has
grown, and the trend is toward zero, not toward accumulation.

The project’s center is **spectral graph theory (SGT)**. Its goal is a broad,
reusable formal neighborhood around SGT: graph and Laplacian theory,
spectral and variational methods, matrix/operator tools, probability, and
bridges that future research can compose.

Scaffold is both a Lean library and a research substrate. It is **pre-release**:
the default `lake build` currently passes, but consumers should pin a [verified
revision](docs/5_QA_SCOREBOARD.md) rather than tracking `main`.

## Status

As of September 5, 2026:

| Check | Result |
| --- | --- |
| Default `lake build` | Passes; the umbrella reaches every public module |
| Explicit cited axioms | 4 |
| Functional theorems/lemmas (`Scaffold/Mathlib` + `Scaffold/Derived`) | 1312 — the public, consumer-facing layer `Scaffold.lean` actually imports |
| QA theorems/lemmas (`Scaffold/QA`) | 6205, with no `sorry` or `admit` under `Scaffold/` — testing infrastructure, not imported by `Scaffold.lean` |

Recent highlights (full per-run history in
[`docs/AGENT_ACTIVITY.md`](docs/AGENT_ACTIVITY.md); per-result detail in each
linked proposal):

- **Alon–Boppana bound** delivered complete end-to-end (Nilli's variational
  route), with the **Ramanujan Expansion Ceiling** as its first theorem
  consumer ([proposal](proposals/alon-boppana-bound.md)), and — named on
  the canonical cycle family — its **asymptotic corollary**: the exact
  cycle distance formula (walk route up, ℤ-potential route down), the
  tree ball and far-apart hypotheses at arbitrary scale, and
  `λ₂(L(C_{4k+8})) ≤ 1/(k+1) → 0` — the program's first parametric
  instantiation, on Mathlib's own `SimpleGraph.cycleGraph` through the
  adapter ([proposal](proposals/cycle-family-alon-boppana-asymptotic.md));
  its QA is now itself **parametric** — the repository's first QA section
  exercising theorems at symbolic scale (`∀ n`/`∀ k`), bracketing the
  tree-ball truth boundary at every cycle size
  ([proposal](proposals/parametric-cycle-qa.md)).
- **Certified stability for Laplacian positional encodings**: the
  general-rank Davis–Kahan pair (`spectralEncodingSubspace_stability`/
  `spectralEncoding_stability`) — the first machine-checked instance of the
  LapPE/SAN subspace-stability class, with the `k = 1` Fiedler pair as
  corollaries and a `k = 2` QA where the bound is exactly attained
  ([proposal](proposals/spectral-positional-encoding-stability.md)) —
  with its **random-graph companion**, the rank-`k` drift pipeline
  (`edgePerturbation_spectralEncoding_drift'`): under Bernoulli edge
  resampling the encoding subspace stays within `s/(γ−s)` of the base's
  with high probability, the separation discharged inline from the base
  gap by proved Weyl — automatic `δ` certification, the delivery's own
  priced follow-on
  ([proposal](proposals/spectral-encoding-drift-pipeline.md)).
- **Certified oversmoothing ceiling from mixing**: depth-form consumers of
  the χ² mixing bound — past a computable depth, every node's propagated
  view is provably within `ε` of stationarity, and any two starts'
  views within `2ε`; QA pins the same graph at two rate certificates
  (depth 3 vs 9 at the same `ε`)
  ([proposal](proposals/message-passing-depth-mixing-bound.md)), with
  its **per-pair resistance refinement** — the four-point contrast of
  the walk law bounded by the mode-rate times
  `√R(x₁,x₂)·√R(y,y')` (the entrywise eigenbasis expansion joined to
  Foster's spectral resistance formula; exact attainment proved on K₃,
  the mode-coverage hypothesis fenced on C₄) — the first bridge
  between the electrical and mixing axes
  ([proposal](proposals/message-passing-depth-mixing-bound.md),
  follow-on record).
- **Spectral sparsification via leverage-score sampling**, complete —
  `matrix_bernstein`'s first real theorem consumer — with the
  **closed-form GNN sampling budget** (`sparsificationBudget`: the
  minimal certified `q` from `(n, ε, δ)`, axiom-free) as its
  practitioner-facing packaging
  ([proposal](proposals/spectral-sparsification-via-leverage-scores.md),
  [usage note](docs/gnn-sparsification-budget.md)).
- **Both Cheeger inequalities** on arbitrary weighted graphs, including the
  volume-weighted (irregular) pair and the higher-order (multiway) easy
  direction (`GraphTheory.Cheeger`, `GraphTheory.Multiway`).
- **The directed / Perron–Frobenius axis**: PageRank, irreducible stationary
  distributions (proved without Perron–Frobenius since the 2026-09-02 Cesàro
  re-proof — power positivity + Krylov–Bogoliubov averaging + min-ratio
  uniqueness), directed mixing, the magnetic Laplacian, and signed-graph
  balance theory.
- **Heat semigroup** and **Krylov / Kaniel–Paige**, both programs complete
  end-to-end with zero admitted axioms.
- **Hermitian functional-calculus bridge**, unifying Tikhonov filtering, the
  heat semigroup, and the magnetic propagator as one construction.
- **Fiedler-subspace stability** and **empirical stationary-distribution
  concentration** — first graph-theoretic consumers of `davis_kahan_sin_theta`
  and `hoeffding_empirical`, respectively.
- **Vertex-degree concentration under edge resampling** —
  `hoeffding_inequality`'s first theorem consumer, the scalar sibling of
  the edge-perturbation tails, with its **Bernstein twin** (the
  variance-adaptive degree tails — `bernstein_inequality`'s and
  `bernstein_bounded_variance`'s first consumers, strictly sharper at
  interior sampling probabilities: `2 exp(−3/5) < 2 exp(−1/4)` proved on
    the fixture) and the **admissibility dissolution** (the window
    family's first unconditional measured event — the admissibility
    conjunct derived from the pair design condition plus the degree
    tails — completed across the family: the floor and swept-cut
    capstone unconditional too). **The scalar concentration stack is now
    axiom-free end to end** — the tail theorems (Hoeffding
    2026-08-30, `hoeffding_lemma_mgf` + the Chernoff assembly; Bernstein
    2026-08-30, the Bennett MGF engine, Errata §8) and the ψ₂-form
    `hoeffding_lemma` itself (2026-08-30, the pointwise-collapse route:
    the defining set sees only the bound and the mass, the sharp
    bound `a/√(log 2)` attained) — every remaining admitted axiom now
    has a theorem consumer.
    ([proposal](proposals/hoeffding-inequality-degree-concentration.md),
    [retirement](proposals/retire-hoeffding-lemma-pointwise-collapse.md)).
- **The matrix master bound** — the first proved slice of the matrix
  concentration retirement route: Tropp's Proposition 3.1 (the
  Laplace-transform step every matrix concentration proof consumes) in
  its two-sided spectral-norm form, with its deterministic engine the
  trace-exponential spectral identity `tr (exp (θ•M)) =
  ∑ exp (θ·λᵢ(M))` (the identity the pinned Mathlib lists as an open
  TODO), the degenerate `V = ∅` corner guarded at birth and fenced in
  QA ([proposal](proposals/matrix-master-bound-first-slice.md)).

The generated [QA Scoreboard](docs/5_QA_SCOREBOARD.md) is the authority for
current counts, verification commands, and limitations.

## Transit map

A hub-and-spoke reading of the SGT core and the seven research axes it
feeds, colored by proof status (proved · admitted axiom · in progress ·
proposed · gated). This is a snapshot, not live data — regenerate it with
`python3 scripts/generate_scaffold_map_svg.py` after a proposal's status
changes; the same underlying data drives a clickable, hoverable version at
[`docs/scaffold_map.html`](docs/scaffold_map.html) (open it locally — it's
plain self-contained HTML/JS, no build step).

<p align="center"><img src="docs/scaffold_map.svg" alt="Hub-and-spoke map of Scaffold's spectral graph theory core and its seven research axes, colored by proof status" width="820"></p>

## Why Scaffold exists

Most of what makes spectral graph theory useful, both Cheeger directions, the
Alon-Boppana bound, the Krylov/Kaniel-Paige program, the heat semigroup, the
full scalar concentration stack, and the Hermitian functional-calculus bridge
among them, is already proved end to end in Lean, with zero admitted axioms.
That is the actual asset: a comprehensive, kernel-checked spectral graph
theory library where you can trust every claim by construction, not by
reputation.

A handful of research-frontier results (4 today, down from 10) are not yet
proved anywhere in Lean, and Mathlib does not expose them either. Rather than
block on every prerequisite or hide the gap behind `sorry`, Scaffold makes
the boundary explicit and disciplined:

- a not-yet-proved published result may enter through a narrow, cited axiom,
  never silently, always named and sourced;
- real definitions and stable APIs make it composable in Lean immediately;
- small QA proofs test the interfaces and selected consequences;
- anything downstream stays honestly conditional on that axiom until it is
  proved locally or replaced upstream, with every retirement recorded in
  [`docs/AGENT_ACTIVITY.md`](docs/AGENT_ACTIVITY.md) and every defect a stress
  test ever found in an admitted axiom logged in
  [`docs/9_ERRATA.md`](docs/9_ERRATA.md), not quietly dropped.

The axiom boundary is the mechanism, not the pitch. The pitch is what it
protects: you always know exactly which claims are proved and which are
assumptions, and the assumption count only ever moves toward zero.

This is stronger than informal derivation because Lean checks the downstream
reasoning. It is weaker than foundational formalization because the admitted
mathematics remains part of the trust base.

### Why spectral graph theory

The center could have been a few other applied-math domains instead; SGT
was chosen over each for a specific tradeoff, not by default.

| Alternative | Its case | Why SGT won instead |
| --- | --- | --- |
| Matrix concentration (Bernstein, Azuma) | Highest immediate utility — nearly every randomized-algorithm and high-dimensional-statistics bound depends on it directly | Needs substantial measure-theoretic setup before any concrete consequence; used here as an admitted bridge (`Probability.Concentration.Matrix.*`), not a starting point |
| Optimization and convex analysis | Interfaces directly with control theory and machine learning | Branches quickly into special cases (convex cones, non-smooth subgradients, constraint qualifications) that resist a clean formalization boundary |
| Classical (unweighted) graph theory | Already well developed in Mathlib; little extra machinery needed | Stays discrete — does not naturally bridge into the continuous linear algebra (eigenvalues, quadratic forms) that connects graphs to the rest of formalized mathematics |

SGT sits at the intersection instead: finite matrices and graphs avoid most
infinite-dimensional measure-theoretic and topological overhead, while its
spectral machinery (eigenvalues, Rayleigh quotients, quadratic forms)
immediately exercises Mathlib's bridges across linear algebra, analysis,
and probability at once. Formalizing SGT is what forces this project to
build reusable interfaces spanning linear algebra (`Spectral`),
combinatorics and expansion (`Cheeger`, `Fiedler`, `Expander`), random
walks (`RandomWalk`, `Normalized`, `Stationary`, `Mixing`), and variational analysis
(Courant–Fischer, the Cheeger bounds) — see "What's here" below — rather
than one isolated result.

### The mushy center and hard crust

Scaffold deliberately keeps two kinds of work separate:

- The **mushy center** is the smallest possible set of research-frontier results
  that we need before their full proofs exist in Lean. Each such result must be
  a named, explicit axiom with a precise statement, a source citation, and a
  clear account of its intended upstream replacement. It is never concealed
  behind `sorry`.
- The **hard crust** is everything that follows mechanically from that center:
  definitions, interfaces, derived theorems, and QA lemmas proved by Lean. This
  work must contain no `sorry` or `admit`, and should make the assumptions on
  which it depends apparent.

Ongoing work should shrink and strengthen the mushy center while expanding the
hard crust. Prefer proving or upstreaming an existing axiom, tightening an
axiom's statement, or deriving a reusable checked consequence over adding a new
assumption. An axiom may be added only when it is cited, necessary for a
concrete SGT milestone, and surrounded by enough hard-crust checks to expose
its intended use.

## The center-out research policy

Ongoing work radiates outward from SGT. We strengthen the center first, add
adjacent mathematics only when it unlocks important SGT obligations, and
advance to applications only when the intervening interfaces are credible.

```mermaid
flowchart LR
    C["Center: spectral graph theory<br/>Laplacians · spectra · Rayleigh · Cheeger"]
    B["Bridge mathematics<br/>perturbation · concentration · matrix updates"]
    F["Reusable SGT extensions<br/>general interfaces · shared tools"]
    A["Research applications<br/>named observables and experiments"]

    C --> B --> F --> A
    B --> C
    F --> B
    A --> F
```

The reverse arrows matter: outer work that exposes a weak definition, missing
assumption, or unusable theorem shape sends us back inward to repair the nearest
dependency. We do not expand the library merely because a topic is adjacent or
interesting.

A proposed task receives priority when it:

1. unlocks a concrete SGT theorem, experiment, or downstream consumer;
2. repairs a load-bearing definition or closes a known proof dependency;
3. reduces the trust surface, removes a placeholder, or replaces an axiom upstream;
4. creates a reusable bridge between SGT and perturbation, probability, or dynamics;
5. can be validated by a focused Lean check, numerical experiment, or citation review;
6. delivers more of the above per unit of complexity and maintenance cost than
   competing work.

Build health, real definitions, and sound theorem shapes take precedence over
adding new surface area. The complete policy lives in
[Strategy](docs/1_STRATEGY.md). Active work is listed in
[proposals](proposals/README.md).

## What's here

The near-term center is general SGT. Public modules currently cover:

| Area | Modules |
| --- | --- |
| Graphs and Laplacians | `GraphTheory.Spectral`, `GraphTheory.SimpleGraphAdapter` |
| Variational spectra | Courant–Fischer, Rayleigh, Cauchy interlacing, the identity-spectrum pin `evals_one` (in `Spectral`), and the **Poincaré inequality family** (`GraphTheory.Poincare`: variance ≤ energy/gap in both the combinatorial and degree-weighted π forms, plus the linear-in-gap edge-expansion bound `λ₂·\|S\|·(\|V\|−\|S\|)/\|V\| ≤ boundary`) |
| Cuts and expansion | `GraphTheory.Cheeger`, `GraphTheory.Fiedler`, `GraphTheory.Expander`, `GraphTheory.Multiway`, `GraphTheory.VariationalTransfer` — both Cheeger directions (regular and volume-weighted), the Expander Mixing Lemma and Hoffman bound, certified-conductance and swept-cut extraction, the higher-order (multiway) easy direction, and the degree eigenvalue sandwich `λₖ(L)/dmax ≤ λₖ(L_sym) ≤ λₖ(L)/dmin` — the irregular family's adversarial fence audit (`proposals/adversarial-fences-irregular-cheeger-family.md`, `IrregularCheeger_QA.lean`'s `IrregularFences` section): negative witnesses for the 19 load-bearing clauses the 2026-08-25/26 delivery left unfenced (the easy direction's `hnn`, the sweep/cut statements' `horth`/`hf0`/`hnn` including the asymmetric `rayleigh`-display cases, the kernel iff's `hconn`, the disconnected-λ₂ theorem's `hnn` (two disjoint signed blocks, `λ₂ = −2`) and `hd` (the isolated vertex's junk `D⁻¹ᐟ²` row makes its eigenvalue `1`), the positivity corollary's `hconn`/`hnn` at a new negative-cut fixture, the Fiedler capstone's `hnn` (λ₂ pinned `0`, the eigenspace characterized, the sweep vector provably a nonzero constant), the sandwich/window wrong-constant `dmin`/`dmax` clauses, the volume extraction's `hy`/`hM` junk corner, and the attainment `hcard` at one vertex), each with an isolation companion (QA-only, zero axioms); the *regular* family's adversarial fence audit (`proposals/adversarial-fences-regular-cheeger-family.md`, `Cheeger_QA.lean`'s `RegularFences` section): negative witnesses for the 17 core + 4 junk-corner clauses of the proved regular Cheeger pair at both spellings, the sweep lemma, and the PSD engine (the signed `!![3,-1;-1,3]]` killing every `hnn`; the wrong-claimed-degree `!![2,1;1,2]]` at `d' = 1/8, 1, 4, 40` killing every `hd`; the zero matrix's junk-conductance corner killing the upper bound's `hdpos`; the asymmetric row-regular `!![4,1;3,2]]` whose symmetric part escapes the claimed degree, killing the PSD engine's `hA`), with the companion audit's decisive recorded finding: four `hdpos` clauses are non-fenceable because the satisfiable nonnegative corner collapses to the zero matrix with the conclusions surviving); the *variational-transfer* family's adversarial fence audit (`proposals/adversarial-fences-variational-transfer-family.md`, `VariationalTransfer_QA.lean`'s `TransferFences` section, the fresh consumption survey's pick at 13 transitive non-QA consumers): 27 hypothesis-form fences over the shelf's unfenced clause surface — the transfer-engine layer's degree clauses at the negative-degree fixture (the junk `√(−1) = 0` collapsing the stretch, `0 ≠ −1` across the degree-weighted pairings, the kernel-cone lift and both cut-test-vector identities), PSD transfer's `hA` at the asymmetric positive-degree fixture and `hnn` at the signed `d = 2`-regular one (`quadForm = −2 < 0`), the congruence lemma's `hP` (`1 ≠ 2` at `P = !![1,1;0,1]]`), the bottom-eigenvalue pin's `hnn` (the signed fixture's bottom normalized eigenvalue `≤ −1`) and `hd` (the all-zero adjacency's `L_sym = 1`, bottom eigenvalue `1 ≠ 0`), the algebraic-connectivity transfer's `hnn` at the signed path with *connected* support (both combinatorial kernel vectors stretch into the normalized kernel, forcing `λ₂ ≤ 0` — connected support does not force a gap once signs enter), the degree sandwich's pointwise engines — headline: the quotient bracket *flips* on signed input exactly as its docstring warns (`−2/3 ≤ −1` false at the connected negative cut with every other hypothesis genuine), plus the wrong-constant `dmin`/`dmax` clauses, the `0 < dmin` guard at the zero-degree corner, and the div-form interface's wrong constant (QA-only, zero axioms; the mixed-pairing clause carried by the diagonal witness at `y = z`) |
| Decidable spectral certificates | `GraphTheory.SpectralCertificates` (ℚ and kernel-verifiable ℤ specification checkers, both soundness-proved) |
| Electrical structure | `GraphTheory.Electrical`, `GraphTheory.ElectricalFlow`, `GraphTheory.Foster` — effective resistance as a genuine metric, Foster's theorem, leverage scores — the core family's **adversarial fence audit** (`proposals/adversarial-fences-effective-resistance-family.md`, `AdversarialFences` sections in `EffectiveResistance_QA.lean` and `ResistanceMetric_QA.lean`): negative witnesses for the definition/Dirichlet/confinement/metric layers' 16 unfenced load-bearing clauses — the existence-flavored statements' `hnn` at a **rank-1 signed 4-cycle** whose connected positive support coexists with a 3-dimensional Laplacian kernel (the demand unsolvable: connected support does not imply solvability once signs enter); the confinement **max** half's `hnn` at a signed overshoot fixture (no 3-vertex signed fixture can kill it — the interior value always solves to a boundary average, why the 2026-08-24 fence only ever killed the min half); both confinement halves' `hconn` at the free-constant-on-a-foreign-component mechanism; the Cauchy–Schwarz and polarization engines' `hA` at an asymmetric nonnegative fixture (the family's only `supportGraph`-free statements); the Dirichlet bound's `hnn`/`hconn`; and the metric residuals' junk corners — each with an isolation companion, plus non-fenceables recorded with mechanisms (the uniqueness `hnn` is provable: solvability forces kernel-invariant voltage differences on symmetric input) (QA-only, zero axioms); the **electrical-flow family's adversarial fence audit** (`proposals/adversarial-fences-electrical-flow-family.md`, `ElectricalFlow_QA.lean`'s `AdversarialFences` section): 22 further clauses of the routing layer — the energy agreement's `hA` at an asymmetric 4-path whose genuine demand potential separates `flowEnergy = 1` from `quadForm = 3/2` (row sums vs column sums); the superposition lemma's support clause killed by a divergence-free cyclic phantom riding zero-conductance pairs (`4 ≠ 2`); Thomson's `hnneg` by a unit flow routing through *both* negative edges of the signed 4-cycle (`0 ≤ −1`); Rayleigh's `hnnegA` by the signed edge's *genuine negative resistance* `−1` (`1 ≤ −1`) and its `hconnA` by the isolated vertex's junk `0` under the dominating path's `2`; and the reinforcement theorems' `hδ`/`hconn` corners (`2 ≤ 1`, `2 ≤ 0`) (QA-only, zero axioms); the **Foster family's adversarial fence audit** (`proposals/adversarial-fences-foster-family.md`, `Foster_QA.lean`'s `FosterFences` section): negative witnesses for the Foster program's 9 unfenced load-bearing clauses — all three graph-level theorems' `hnn` at the signed rank-1 fixture (the zero-eigenvalue count forced `≥ 2` by two non-parallel kernel vectors; the spectral kernel's RHS strictly positive against the junk-fallback LHS through the fixture-local rank-1 SOS `quadForm L f = (s ⬝ f)²`; the ordered sum itself `0 ≠ 3` since *every* off-diagonal demand is unsolvable by the injectivity of `x ↦ (w₁ x, w₂ x)` over the two kernel generators) and `hconn` at the disconnected fixture (each component contributing its own zero eigenvalue; the ordered sum `4 ≠ 2·3`), plus the leverage corollary's `hcard` division-guard junk corner `0/0` at a one-vertex fixture (QA-only, zero axioms); the **kernel-bridge family's adversarial fence audit** (`proposals/adversarial-fences-kernel-bridge-family.md`, `KernelBridge_QA.lean`'s `BridgeFences` section): negative witnesses for the kernel-equality bridge and its weighted center characterization chain's 12 unfenced load-bearing clauses at three new signed/asymmetric fixtures — every `hnonneg` clause of the iff (both directions: the junk-trivial RHS at an edgeless-support negative edge; a genuine kernel vector nonconstant on *connected* signed support), of the bridge (both orientations), of the dimension statement (both witnesses: `1 ≠ 2` and `2 ≤ finrank ≠ 1`), of the span/exists-const forms (with `hconn` kept genuine by the connected-support fixture), and of the walk/pos-weight engines at the mechanism level — plus the family's only `supportGraph`-free statement's `hA` at an asymmetric *nonnegative* sink star where only symmetry fails (`1 ≠ 2`) (QA-only, zero axioms) |
| Heat semigroup | `GraphTheory.Heat` — the diffusion operator `e^{-tL}`: semigroup law, mass conservation, eigenmode decay, the connected-graph DC limit, the derivative/remainder bounds at `t = 0`, and heat-variance decay (`Var(e^{-tL}f) ≤ e^{−2tλ₂}Var(f)`, the Poincaré family's consumer, hypothesis-minimal — exact at `λ₂ = 0`); plus the walk/normalized twin pair `e^{-tL_walk}`/`e^{-tL_sym}` with the `√D`-conjugation between them and the π-weighted variance decay at rate `λ₂(L_sym)` (the continuous-time mixing engine); program complete |
| Walks and mixing | `GraphTheory.RandomWalk`, `GraphTheory.Normalized`, `GraphTheory.Stationary`, `GraphTheory.Mixing` — the ℓ²-mixing proxy and the geometric-decay mixing bound — plus `GraphTheory.Oversmoothing`, the certified depth past which propagated views are provably ε-close to stationarity, the per-pair resistance contrast bound (the walk law's four-point contrast against `√R·√R` of the two pairs), and the **total-variation mixing conversion** (`tvDistance` with `TV ≤ (1/2)·√χ²` at the sharp classical constant, and the depth-form TV ceiling — the field-standard `t_mix(ε)` statement form, with its two-start `2ε` twin) , and the continuous-time χ² mixing bound (intrinsic rate, no caller certificate, connectivity-free) with the **continuous-time mixing time** `contMixingTimeFrom` — the per-start `t_mix(ε)` at LPW ch. 20's `∀ s ≥ t` reading, its spectral ceiling `t_mix(ε) ≤ max 0 (ln(√((πx)⁻¹−1)/(2ε))/λ₂(L_sym))`, the continuous walk law and its TV conversion twins, and ε-antitonicity — and the **Poisson bridge**: the Poissonization identity `ν^cont_t = ∑'ₖ e^{−t}tᵏ/k!·ν_k`, the `Pᵀ` TV-contraction toolkit with discrete TV monotonicity, and the continuous↔discrete comparability `TV_cont(t) ≤ ∑_{k<m} e^{−t}tᵏ/k! + TV_disc(m)` with its discrete-certificate transfer corollary — and the **discrete mixing time** `walkMixingTimeFrom` (the `t_mix(ε)` object at LPW ch. 20's per-start reading, the twin of the continuous object), whose attainment specification (a *minimum*, by well-ordering) discharges that corollary's certificate clause, with its own spectral ceiling `t_mix(ε) ≤ ⌈log(√C/(2ε))/log(1/r)⌉`  — and the **spectral mixing floor** (the program's first lower-bound family, the over-squashing floor delivered on its own named route): the exact law-level test-function evolution at arbitrary `L_sym` eigenpairs, the TV and χ² floors `(1/2)|1−μ|^t·|v x|/(√D x·c) ≤ TV` and `(1−μ)^{2t}(v x)²/(π x·‖v‖²) ≤ χ²` (periodic modes never decay — the chains no ceiling reaches), the `t_mix` floor gate, and the log-form floor `⌈log(|v x|/(√D x·2εc))/log(1/|1−μ|)⌉ ≤ t_mix` — the classical eigenvalue lower bound on mixing time, completing the two-sided depth bracket — and the **uniform mixing time** `walkMixingTime` (LPW's field-standard worst-case-start `t_mix(ε)`) with the **submultiplicativity class** it unlocks: LPW's two distances `d(t)`/`d̄(t)`, the sharp Dobrushin contraction `TV(μ(Pᵀ)ᵗ, ν(Pᵀ)ᵗ) ≤ TV(μ,ν)·d(t)` at equal masses, the classical `d(s+t) ≤ d(s)d(t)` and `d̄(s+t) ≤ d̄(s)d(t)`, and the ε-escalation corollary — one certified evaluation time yields every ε-level mixing time (LPW's `t_mix := t_mix(1/4)` convention's engine)  — and the **entropy leg** (`proposals/entropy-mixing-pinsker.md`): Pinsker's inequality `TV ≤ √(D/2)` in vector form, the entropy–χ² bridge, entropy decay along the walk (discrete certificate form and the continuous-time intrinsic-rate twin), and the entropy *floor* (Pinsker × the spectral TV floor — `InformationTheory.Entropy`'s first graph-level consumers, zero axioms) — and the **lazy walk** (`proposals/lazy-walk-mixing.md`): the operator `P_L = (P+I)/2` (LPW ch. 5's periodicity fix) with the intrinsic-rate χ² mixing bound `χ²_lazy ≤ (1 − λ₂/2)^{2t}·((πx)⁻¹−1)` — connectivity the only graph hypothesis, so the discrete program's certificate families become satisfiable on every bipartite graph — its TV/entropy twins, and the signless-Laplacian SOS engine `μ(L_sym) ≤ 2` (zero axioms) — and the **lazy mixing time** (`proposals/lazy-mixing-time-objects.md`): the `t_mix(ε)` object at the lazy law with its certificate/attainment package and intrinsic-rate spectral ceiling `t_mix(ε) ≤ ⌈log(√((πx)⁻¹−1)/(2ε))/log(1/(1−λ₂/2))⌉`, the depth-form TV lazy ceiling, and the entrywise lazy ceiling at the intrinsic rate — the plain objects' junk corner (bipartite graphs: empty witness set) closed by genuine lazy mixing times, with `λ₂(L_sym) ≤ 2` capping the whole normalized spectrum in `[0, 2]` (zero axioms) — and the **empirical lazy sampling guarantee** (`proposals/empirical-lazy-stationary-sampling.md`): the empirical-stationary capstone's lazy twins in `Derived/EmpiricalStationary.lean` — `n` simulated lazy trajectories estimate `π i` to `ε` at a Hoeffding tail past the lazy ceiling's own depth threshold, with the bias computed at the intrinsic rate `(1 − λ₂/2)^t₀` under connectivity alone (no caller-supplied rate certificate), instantiating on exactly the bipartite class where the plain program's certificate is provably unsatisfiable (zero axioms) — and the **Doeblin TV contraction** (`proposals/doeblintv-tv-contraction-pagerank-rate.md`): the directed axis' first TV statement — `TV(μ ᵥ* Q, ν ᵥ* Q) ≤ (1 − |V|δ)·TV(μ, ν)` for row-stochastic `Q` with entries `≥ δ` at equal masses (hypothesis-minimal, the Doeblin range engine's second consumer through the dual/test-function pairing), with the block assembly and the PageRank `α^t` rate as its named consumer — and the **equal-mass entrywise TV extraction** `|μ i − ν i| ≤ TV(μ, ν)` (constant sharp; the directed bias term's engine), and the **matrix-level Dobrushin coefficient** `tvDobrushinCoeff` with the sharp contraction `TV(μ ᵥ* Q, ν ᵥ* Q) ≤ TV(μ,ν)·δ(Q)` at equal masses and generic power submultiplicativity — the undirected uniform delivery's mechanism promoted to any row action (zero axioms) — and the **primitivity supplier at the walk** (`proposals/primitivity-supplier-plain-walk.md`): `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk` — on a connected support graph with a single odd closed walk, the walk matrix is primitive (reversal handled at the `Walk` level; `Odd p.length` the honest interface, the pinned Mathlib having no `SimpleGraph.Bipartite`), with two consumers: the plain walk's first mixing rate `TV(ν_t x, π) ≤ (1 − |V|δ)^{t/m}` with **no spectral certificate and no caller-supplied `r`** (the intrinsic-rate family's non-bipartite member), and the retired `primitive_power_tendsto`'s first undirected consumer `walkDistribution_tendsto_stationaryVec` (zero axioms) — and the **adversarial fence completion for the TV/Dobrushin engines** (`proposals/adversarial-fences-tv-dobrushin-engines.md`, `DirectedMixing_QA.lean` Section I): negative witnesses for every load-bearing hypothesis of the directed TV engine family the same day's deliveries left unfenced — the equal-mass clauses of both TV contractions, the row-sum and nonnegativity clauses of non-expansiveness, the row-sum clause of Dobrushin submultiplicativity, and the zero-mass clauses of both pairing cores — each with an isolation companion proving the refuted clause is exactly what fails at the fixture (QA-only, zero axioms) — and the **adversarial fence audit of the lazy family** (`proposals/adversarial-fences-lazy-family.md`, `Mixing_QA.lean`'s `LazyFences` section): the second mixing-cascade family audited — negative witnesses for the lazy family's ten unfenced load-bearing hypotheses (the `hd` clauses of row-stochasticity, mass conservation, and the `t = 0` χ² normalization at a zero-degree fixture; the `hnn` clauses of operator/law nonnegativity at a negative off-diagonal fixture; the `hA` clauses of detailed balance, stationarity, and attainment persistence at an asymmetric fixture whose lazy law hits `π` exactly at `t = 1` and leaves it at `t = 2`; and both certificate clauses of the public lazy ℓ²(π) contraction engine, with the triangle's `3/2`-mode and the edge's constant mode as the refuting directions), each with an isolation companion,  — and the **adversarial fence audit of the entropy family** (`proposals/adversarial-fences-entropy-family.md`, `Entropy_QA.lean`'s Section F + `Mixing_QA.lean`'s `EntropyFences` section): the third mixing-cascade family audited — negative witnesses for the entropy family's 28 unfenced load-bearing clauses (every mass clause of the generic KL/entropy layer incl. the transcendental `H(1/3,…) = (4/3)·log 3 > log 4` fence by `3⁴ > 4³`; both mass clauses of Pinsker via junk-negative divergences; the decay form's rate certificate; `hnn`/`ht` of the continuous nonneg plumbing through closed-form heat kernels at `negOffAdj` and the backward semigroup on `K₂`; `hA`/`hd` of mass conservation at a new idempotent-Laplacian asymmetric swap and the junk zero law; and all four analytic clauses of the entropy floor), each with isolation companions, plus the recorded non-fenceables (junk log-of-negative contamination, vacuous empty-type corners, proof-shaped `hconn`, and three removable-hypothesis findings incl. the heat kernel `e^{−t}·e^{tP} ≥ 0` argument for the continuous nonneg `hA` clauses) (QA-only, zero axioms) — and the **adversarial fence audit of the Poisson-bridge family** (`proposals/adversarial-fences-poisson-bridge-family.md`, `Mixing_QA.lean`'s `PoissonFences` section): the fourth mixing-cascade family audited — negative witnesses for the continuous↔discrete hinge's 28 unfenced load-bearing clauses (the simplex-diameter lemma's four mass clauses; the head–tail split's summability clause; the TV convexity bound's `hc`/`hc1` and `hν`/`hν1` — the corpus's first **divergent-tsum junk** fences: summable weights against growing laws junk both sides to `0` against the honest left TV; the Poisson weight's negative time; the `hnn` clauses of the TV ≤ 1 bound, the adjoint-walk contraction and its power twin, and discrete TV monotonicity; the `hA` clauses of the whole Poissonization identity triple — the identity *is* reversibility — of the stationary power, and of monotonicity at a new asymmetric-flow fixture; the rate theorems' `hA` at `t = 2`; the `ht` clauses at `t = −1` on the edge; and the transfer corollary's `htail` on the triangle, refuted from a new series bound `e < 3`), each with isolation companions, plus sixteen recorded non-fenceables with mechanisms (the ten `hd` clauses survive on truth as substochastic algebra; the convexity bound needs no target structure; the factorial beats spectral growth) (QA-only, zero axioms) — and the **adversarial fence audit of the primitivity-supplier family** (`proposals/adversarial-fences-primitivity-supplier-family.md`, `EmpiricalStationary_QA.lean`'s `PrimitivityFences` section): the fifth and last mixing-cascade family audited — negative witnesses for the supplier family's 21 unfenced load-bearing clauses (the concatenation/bounce `hnn`/seed/step clauses at off-path negative entries; the supplier's `hreach` at the identity, `htwo` at the directed 3-cycle permutation, `hodd` at the swap, and `hnn` at the exact-cube rotation `!![1,−3;1,1]` whose `M³ = −8·1` signs every power; the walk-to-power bridge's `hnn` at a negative-diagonal chord; the walk-level supplier's and the convergence corollary's `hnn` at the negative-diagonal triangle whose closed forms carry the eigenvalue `−11/4`, their `hconn` at the triangle⊕isolated-vertex fixture with identically-zero cross-block power entries, and their `hp` at `K₂`; the Doeblin rate's `hle` (base gone negative at `δ = 1`) and its `hA` at the asymmetric loop where `π` is not stationary) — and the same proposal's **capstone consumer fences** (2026-09-03): negative witnesses for the self-contained capstone's two deferred graph clauses, `hp` at `K₂` (connectivity genuine, every closed walk even — the sampling measure concentrates on the all-zero trajectory, deviation `1/2` at full mass `1 > 2 exp(−4)`) and `hconn` at `triIso4` (a genuine odd walk, but the absorbing vertex `3`'s law is `δ₃` forever, deviation `6/7` at full mass), through the point-mass cylinder helper `toMeasure_cyl_singleton_one` — the theorem's falsification surface completed (QA-only, zero axioms) — and the lazy audit's **priced follow-on fences** (2026-09-03, same proposal's follow-on record): the conjugated-norm contraction twin's two certificate clauses fenced (the √D-weighted mirrors of the ℓ²(π) pair — `hrate` on the triangle at the `3/2`-mode direction, `LHS = 1/4 > 1/16 = RHS`; `hmode` on the edge at the constant zero mode with the genuine `r = 0`, `2 > 0`), and the lazy `t_mix` object's `_spec` witness-clause junk corner fenced at the disconnected bipartite fixture `K₂ ⊕ K₂` (the full lazy-law closed form — `δ₀` at zero, the component-stationary `(1/2,1/2,0,0)` after; `TV = 3/4`/`1/2`, never below `1/8`; no witness, `t_mix = sInf ∅ = 0`, dropped-`hne` conclusion refuted at `s = 0` — every structural hypothesis genuine, connectivity exactly the failure: laziness repairs periodicity, not disconnection) — the last priced QA items in the mixing cascade closed (QA-only, zero axioms) — and the **plain walk's spectral certificate** (`proposals/spectral-certificate-plain-walk.md`): the strict signless engine (connected + an odd closed walk ⟹ every `L_sym` eigenvalue `< 2`, through the signless SOS: a `μ = 2` eigenvector unstretches to an edge-flipping potential, which the odd walk zeroes and connectivity propagates to zero everywhere — contradicting the unit eigenvector), the computed certificates `∃ r < 1` / `∃ r ∈ (0,1)` at `r := max (1 − λ₂) (λ_max − 1)` (connectivity's `0 < λ₂` + the engine's `λ_max < 2` + the below-gap plumbing), and the χ²/TV/entrywise max-rate joins — the plain family's display twin of the lazy intrinsic rate, contractive on exactly the non-bipartite class (the depth-form oversmoothing ceiling's non-lazy walk), with the `r = 0` corner honest at the looped triangle (QA-only at the fences, zero axioms) — and the certificate proposal's **depth-form join landed** (2026-09-03): `walkDistribution_sub_stationaryVec_le_of_depth_of_odd_walk`, the plain family's first certificate-free depth ceiling at the inflated computed rate, with the odd-walk clause fenced load-bearing at `C₄` by the junk-threshold route (the saturated display's `log 1 = 0` makes the threshold hypothesis vacuous while the conclusion fails — zero axioms) — and its **two-start indistinguishability twin** (2026-09-04): `walkDistribution_sub_walkDistribution_le_of_depth_of_odd_walk`, past both starts' own computed thresholds any two `t`-step views within `2ε` — the "representations become indistinguishable" statement certificate-free, with a genuinely two-start C₄ fence (opposite-parity starts, a witness shape the one-start fence cannot exhibit) — and the **adversarial fence audit of the normalized-Laplacian family** (`proposals/adversarial-fences-normalized-family.md`, the `AdversarialFences` section of `Normalized_QA.lean`, 2026-09-04): negative witnesses for all 27 load-bearing clauses of the congruence-bridge root the whole mixing program consumes — the headline finding a P4-class truth at scale: at *symmetric zero-degree* fixtures the dropped-`hd` statements of the bridge, the left-multiplied congruence, the commutation form, and the power transfer are provable (the junk kills both sides identically), the genuine breaker being the negative-degree row where `(deg)⁻¹` is genuine while the square roots vanish — fifteen clauses killed by the single Fin 2 fixture `!![-2,1;1,0]]` (`L_sym` = identity, `P = !![2,−1;1,0]]`, all rational), the eigenbasis instantiations fenced without eigenvalue pins (orthonormality-witness index), and the transferred-spectrum existential dead by row equations (QA-only, zero axioms) |

| Directed operators | `GraphTheory.Directed` — out/in-degree, directed handshaking, the directed normalized Laplacian |
| Krylov methods and Chebyshev polynomials | `GraphTheory.Krylov` — the Lanczos/Kaniel–Paige program, complete end-to-end |
| Polynomial filters and band projection | `GraphTheory.PolyFilter` — filter-agnostic band-projector approximation, with power-method and Chebyshev instantiations |
| Nonnegative-matrix spectral theory | `LinearAlgebra.PerronFrobenius` (the admitted Perron–Frobenius axiom) and `LinearAlgebra.PrimitiveConvergence` — the primitive power limit **proved 2026-09-02** by the Doeblin/Dobrushin contraction route (retired from axiom; the entrywise-range engine `entryRange_mulVec_le_of_pos_entries` is public and reusable), plus the **primitivity supplier** `isPrimitive_of_pow_pos_of_odd_loop` (2026-09-02: strong connectivity + every vertex on a positive 2-cycle and an odd closed walk ⟹ `IsPrimitive`, by the two-parity covering — the combinatorial fact that connects graph structure to the retired theorem's hypothesis; zero axioms) |
| Irreducible stationary distributions | `GraphTheory.IrreducibleStationary` — Perron–Frobenius's first theorem consumer, hard crust since the 2026-09-02 Cesàro re-proof (`proposals/cesaro-stationary-existence.md`: power positivity from strong connectivity, the Krylov–Bogoliubov cluster lemma `exists_cluster_stationary_of_orbit`, existence for any row-stochastic action with no irreducibility, strict positivity, min-ratio uniqueness — `perron_frobenius` now has zero non-QA consumers) |
| PageRank | `GraphTheory.PageRank` — the teleportation-regularized Google matrix, existence and uniqueness on reducible input (hard crust since 2026-09-02) |
| Directed mixing | `GraphTheory.DirectedMixing` — `primitive_power_tendsto`'s first consumer, the PageRank power-iteration theorem (hard crust since that admission's 2026-09-02 retirement), plus the rate form `pageRank_tvDistance_le` (`TV ≤ α^t·TV₀`, the field-standard PageRank rate via the mixing layer's Doeblin TV contraction), the per-start Google-walk law `pageRankDistribution` (probability-certified), the ⌈log⌉-threshold depth form of the rate, and **the directed mixing time** `pageRankMixingTimeFrom` — the `t_mix` object family's missing directed sibling, with its α-ceiling `t_mix(ε) ≤ ⌈log(TV(δ_x,π)/ε)/log(1/α)⌉` and attainment package; the named consumer is the empirical PageRank capstone in `Derived/EmpiricalStationary.lean` (n simulated random-surfer trajectories estimate `π i` to `ε` past the object's own threshold — on directed input the only mixing route, the symmetric toolkit being unavailable there) — and **the directed uniform (worst-start) `t_mix`** `pageRankMixingTime` (the `t_mix` object family's last missing member): LPW's two distances `d`/`d̄` at the Google law, the submultiplicativity class and ε-escalation corollaries through the matrix-level Dobrushin engine, the refined α-ceiling `t_mix(ε) ≤ ⌈log(d̄(0)/ε)/log(1/α)⌉` with its display form, the well-posedness witness supplier, and the worst-start sampling capstone `empiricalPageRank_uniform_tail_of_depth` — one start-independent threshold certifies `n` simulated trajectories for *every* start simultaneously (zero axioms) |
| Magnetic Laplacian | `GraphTheory.Magnetic` — the shelf's first complex Hermitian object; flux/gauge characterization |
| Signed graphs | `GraphTheory.Signed` — the signed Laplacian; Harary's balance theorem in kernel form |
| Alon–Boppana program | `GraphTheory.AlonBoppana` — complete end-to-end via Nilli's variational route; its first theorem consumer is the Ramanujan Expansion Ceiling |
| Hermitian functional calculus | `GraphTheory.FunctionalCalculus` — the Scaffold–Mathlib bridge; recovers Tikhonov filtering, the heat semigroup, and the magnetic propagator as one calculus |
| Cluster projector | `GraphTheory.ClusterProjector` — the spectral projector onto an arbitrary eigenvalue set; together with `GraphTheory.Band` its QA now carries the **band-projector family's adversarial fence audit** (`proposals/adversarial-fences-band-projector-family.md`, `Band_QA.lean`'s `BandFences` + `ClusterProjector_QA.lean`'s `ClusterFences`, the Step-0 consumption survey's pick — this neighborhood feeds the set-form Davis–Kahan bridge): 29 hypothesis-form negative witnesses closing every unfenced load-bearing clause, headline fences at the negated junk band `B(4,0] = −1` (non-idempotence `(−1)² ≠ −1`, annihilation `−v ≠ 0`, the Hilbert identification `x ≠ −x` through the surjective negation range, and the closest-point bound's `‖2x‖ ≤ ‖x‖` collapse) and at the band agreement's own docstring corner (`Ioc 6 (−1) = ∅` against `−diag(1,1,0) ≠ 0`), with the shared-mode theorem's `hab`/`hcd` recorded non-fenceable by the trivial-fixed-space mechanism (a negated band's fixed vectors are already zero — the dropped-guard statement is provable) |
| Perturbation | `Analysis.OperatorTheory.Perturbation.{Weyl,DavisKahan,BandDavisKahan,ProjectionGap,Duhamel}` — Weyl's inequality, Davis–Kahan sin Θ, and the band/cluster projector-stability family; the core chain's QA (`Weyl_QA`/`DavisKahan_QA`/`ProjectionGap_QA`) now carries the **Davis–Kahan core family's adversarial fence audit** (`proposals/adversarial-fences-davis-kahan-core-family.md`, the fresh Step-0 consumption survey's pick — these four shelves are the library's four most-consumed unaudited surfaces at 4–7 non-QA consumers each): 20 hypothesis-form negative witnesses, headline fences at the Duhamel bound's inflated-window `hcl` (a new threshold-`1` projector pin, the witness squaring `‖(1−Q)P‖² ≥ 1/10 > (3/400)²`), the negative-`δ`/negative-denominator corners of the sin-Θ bound and `hab`, the zero-matrix tie refuting the rank pin's no-tie clause (`rank 2 ≠ 1` through `spectralProjector_eq_one`), and the two equal-rank identities' signature-free clause surfaces at trivial fixtures — with the Weyl additive pair's `hcard` recorded non-fenceable by a distinct proof-term-in-display mechanism (the conclusion's own `by omega` consumes it) |
| Concentration | `Probability.Concentration.Scalar.*`, `Probability.Concentration.Matrix.*` |
| Spectral sparsification | `GraphTheory.Sparsification`, `Derived.SparsificationTail`, `Probability.BernoulliProduct` — leverage-score sampling; `matrix_bernstein`'s first real theorem consumer; the `(1±ε)` sparsifier tail, its `q ~ log n/ε²` budget, and the graph-vector form on the sampled Laplacian — the deterministic core's **adversarial fence audit** (`proposals/adversarial-fences-sparsification-core-family.md`, `Sparsification_QA.lean`'s `CoreFences` section, the electrical cluster's last QA family): negative witnesses for the core's 15 unfenced load-bearing clauses — the eigenvalue/leverage/budget/projector/deviation layer's `hnn` clauses (the rank-1 signed 4-cycle's ordered-pair budget summing to `1 ≠ 3`; the nonpositive-spectrum fixture's zero edge vectors against a nonzero image projector, killing the rank-one-sum, quadratic-form, trace, and exact-deviation identities at one mechanism; the signed fixture's negative-pair leverage share `0 ≠ 1`), the bilinear Dirichlet identity's `hA` at an asymmetric `Fin 2` (`3 ≠ 4` — the unequal off-diagonals against the symmetrized action), the trace identity's `hconn` at the disconnected fixture through the delivered Foster kernel-count engine, and the probability/weight/centering/variance/PSD layer's `hq` clauses plus the Bernoulli second moment's `hpne` at `K₂` — with the headline non-fenceable finding that the junk-√ zero edge vector acts as an *automatic sign guard* on the sampled Laplacian's PSD theorem (QA-only, zero axioms) |
| Edge-perturbation concentration | `GraphTheory.EdgePerturbation`, `Derived.EdgePerturbationTail`, `Derived.EdgePerturbationDrift` — centered Bernoulli edge-Laplacian perturbations; `matrix_hoeffding`'s first theorem consumer; the norm/quadratic-form tails, the eigenvalue-level (spectral-gap) tail via proved Weyl, the high-probability Fiedler-drift pipeline (with its matched-threshold `s/(γ−s)` sharpening), the Cheeger-driven connectivity window, its irregular (normalized) sibling via the degree sandwich, and the swept-Fiedler-cut capstone (connected + certified cut of the resampled graph), the C₄ dropped-guard refutation of its floor-positivity hypothesis, and the per-vertex degree-deviation tail (`hoeffding_inequality`'s first theorem consumer, with the all-vertices union bound) plus its variance-adaptive Bernstein twin (`bernstein_inequality`'s and `bernstein_bounded_variance`'s first consumers, at the true variance statistic `∑ₑ w² p (1−p)`) and the admissibility dissolution (the unconditional connectivity window: `perturbAdmissible` derived from the pair design condition `p e + p eᵀ ≤ 1` plus the degree tails — completed across the family, the floor and swept-cut capstone unconditional too, with the strict-containment witness proving the measured event genuinely enlarged) |
| Concentration → subspace-stability pipeline | `Derived.EdgePerturbationDrift` — high-probability Fiedler-subspace and Fiedler-line rotation under random edge resampling (`edgePerturbation_fiedlerLine_drift`), composing `fiedlerLine_stability` with `edgePerturbation_norm_tail` through the packaging identity `laplacian (perturbWeight A p ω) = ∑ₑ perturbSummand` and the Laplacian linearity package (`laplacian_smul`/`laplacian_sum`); since 2026-08-31 the **rank-`k` spectral-encoding drift pipeline** (`edgePerturbation_spectralEncodingSubspace_drift{'}`, `edgePerturbation_spectralEncoding_drift{'}`) — the same pipeline at arbitrary encoding rank, the separation discharged inline from the base graph's rank-`k` gap by proved Weyl at index `k+1` (automatic `δ` certification) |
| Empirical stationary distribution | `Probability.IIDProduct`, `Derived.EmpiricalStationary` — the fixed-time empirical tail (`hoeffding_empirical`'s first theorem consumer, hard crust since that axiom's retirement) and the stationarity-limit form: past the oversmoothing depth, `n` sampled trajectories estimate `π` to `ε` at `2 exp(−nε²/2)` — the depth certificate as a sampling guarantee — plus the lazy twins (bias at the computed intrinsic rate, instantiating on the bipartite class where the plain certificate is provably unsatisfiable), the PageRank capstones, and **the self-contained PageRank capstone** `empiricalPageRank_tail_selfcontained_of_depth` (2026-09-02): the program's target produced by the theorem itself — `∃ π` (positive, mass one, stationary at the Google walk, via the re-proved `exists_pageRankVec`) plus a single `(α, ε)`-computable display threshold certifying `n` simulated trajectories for every start — no caller-supplied stationarity anywhere — and **the plain family's self-contained twin** `empiricalWalkDistribution_tail_selfcontained_of_depth` (2026-09-02, `proposals/primitivity-supplier-plain-walk.md`): on a connected graph with a single odd closed walk, the theorem produces the threshold itself — `∃ t₀` past which `n` simulated walk trajectories estimate `π i` to `ε` at `2 exp(−nε²/2)` for every start simultaneously, the rate supplied by the primitivity supplier rather than any caller certificate (the PageRank twin's `(α, ε)` display honestly existential here; zero axioms) |
| Finite-distribution entropy | `InformationTheory.Entropy` (relative entropy and Shannon entropy, Gibbs' inequality, the entropy maximum — all proved) |
| Discrete-affine dynamics | `Dynamics.DiscreteAffine` (finite-vector geometric decay and affine-iteration convergence, all proved) |
| Matrix updates | `Core.MatrixUpdates` (Woodbury, Sherman–Morrison) |

Outward work must improve one of those interfaces or make a concrete, broadly
reusable connection. The existing persistence modules
(`GraphTheory.Dynamics`, `Derived.EventStream`, `Derived.ProjectorDrift`) do
not set this agenda; they are a retained example whose tail and projector-drift
theorems remain conditional on Matrix Azuma alone (Davis–Kahan and Weyl
are proved since 2026-08-21/20).

See [Spectral Theory](docs/3_SPECTRAL_THEORY.md) for the status of that
example, and the [SGT Radar](docs/7_SGT_RADAR.md) for coverage scores.

### SGT coverage snapshot

Last assessed: August 31, 2026. Scores reflect usable, verified coverage on a
0–5 scale; see the [full radar and evidence](docs/7_SGT_RADAR.md).

| Area | Coverage |
| --- | ---: |
| Graph and Laplacian models | 4.0 / 5 |
| Spectral linear algebra | 4.5 / 5 |
| Variational and functional methods | 4.0 / 5 |
| Cuts, expansion, and clustering | 5.0 / 5 |
| Random walks and diffusion | 4.5 / 5 |
| Combinatorial and electrical structure | 4.5 / 5 |
| Perturbation, randomness, and algorithms | 4.5 / 5 |
| Adjacent systems interfaces | 1.0 / 5 |

Assurance quality is assessed separately in the full radar; subject coverage
and trust level are not combined into one score.

## Trust model

Citations and explicit axioms belong in the mushy center; checked Lean proofs
belong in the hard crust. Do not describe an axiom-backed result as fully
formalized, and do not use `sorry` to move a result across that boundary.

| Artifact | What it establishes | What it does not establish |
| --- | --- | --- |
| Real Lean definition | A precise, typechecked object | That it is the best model of the application |
| Explicit cited axiom | A visible assumption usable by Lean | A proof or machine-verified transcription of the source |
| QA lemma with a real proof | A checked consequence of its dependencies | The truth of any axioms it uses |
| Axiom-backed derived theorem | Correct deduction relative to the trust base | A foundationally proved theorem |
| Numerical or domain experiment | Evidence for specified behavior | A general mathematical proof |

Project documentation uses these labels distinctly. Citation review,
compilation, mathematical review, and empirical validation are separate gates.

## Repository map

```text
Scaffold/Mathlib/   public definitions and explicit axiom APIs
Scaffold/QA/        fully proved interface checks
Scaffold/Derived/   axiom-backed derived theorems (checked deductions)
Scaffold/Internal/  internal utilities
index/              source mappings and domain maps
docs/               canonical strategy, architecture, theory, partnerships, and QA
governance/         contribution, maintenance, conduct, and release process
research/papers/    reference papers and research artifacts
research/archive/   provenance and superseded reports—not current policy
scripts/            documentation and policy checks
proposals/          active priority list and delivered records
```

`Scaffold/Derived/` holds derived theorems: Lean-checked deductions whose
conclusions remain conditional on the axioms they consume. Its first two
modules are a retained persistence example: `EventStream.lean` derives an
Azuma tail bound on a random event-driven graph stream, and
`ProjectorDrift.lean` derives a high-probability endpoint projector-drift
bound. They are not a standing expansion target.

The remaining root files are repository entry points or tool configuration:
`Scaffold.lean` is the Lake library root; `lakefile.lean`,
`lake-manifest.json`, and `lean-toolchain` pin the build; and `opencode.json`
configures project-local agent tooling. Lean modules otherwise belong under
`Scaffold/`.

## Get started

Pinned toolchain: Lean 4.14.0 (see `lean-toolchain`; Mathlib is required at
the matching `v4.14.0` tag).

```sh
lake build
python3 scripts/generate_qa_scoreboard.py
python3 scripts/lint_axioms.py
python3 scripts/check_citations.py
python3 scripts/check_markdown_links.py
```

`lake build` builds the library root `Scaffold.lean`. Downstream consumers
should prefer a narrow import over that umbrella.

## Intended consumption

Once the scoreboard reports a clean build for the required modules, a Lake
project can pin Scaffold as follows:

```lean
require scaffold from git
  "https://github.com/marcospolanco/scaffold.git" @ "<verified-revision>"
```

Representative narrow imports:

```lean
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.Probability.Concentration.Matrix.Bernstein
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan
```

## Working on Scaffold

Before adding a new domain or theorem family:

1. identify the SGT obligation or downstream experiment it unlocks;
2. map the shortest dependency path back to the SGT center;
3. compare its leverage against repairing existing definitions, imports,
   citations, and axioms;
4. define the smallest composable interface;
5. record whether each dependency is proved, axiom-backed, experimental, or
   conjectural;
6. add proportionate QA and run the narrowest meaningful verification.

See [Contributing](governance/CONTRIBUTING.md) for the review workflow.

Non-interactive agent runs use `scripts/opencode-pursue`. The project agent
follows `AGENTS.md`, maintains the [execution plan](docs/EXECUTION_PLAN.md)
and [activity log](docs/AGENT_ACTIVITY.md), and is denied publishing or
destructive Git commands. See [`scripts/README.md`](scripts/README.md) for
the safety boundary and invocation.

## Canonical documentation

- [Strategy](docs/1_STRATEGY.md) — mission and center-out prioritization.
- [Architecture](docs/2_ARCHITECTURE.md) — axiom admission, QA, citations, and
  upstream replacement.
- [Spectral Theory](docs/3_SPECTRAL_THEORY.md) — retained persistence example.
- [Partnerships](docs/4_PARTNERSHIPS.md) — dated, time-sensitive research landscape.
- [QA Scoreboard](docs/5_QA_SCOREBOARD.md) — generated metrics and recorded verification.
- [SGT Backlog](docs/6_SGT_BACKLOG.md) — ranked, center-first work queue.
- [SGT Radar](docs/7_SGT_RADAR.md) — evidence-scored coverage of the SGT neighborhood.
- [Mathlib Coverage Map](docs/8_MATHLIB_COVERAGE_MAP.md) — dated survey of the
  pinned Mathlib itself, distinct from Scaffold's own coverage.
- [Errata](docs/9_ERRATA.md) — every admitted axiom or theorem statement
  found materially false or inconsistent after landing, and how it was
  repaired; the evidence trail behind the trust model above.
- [Proposals](proposals/README.md) — active priority list and delivered records.
- [Traction Plan](docs/traction-plan.md) — promotion plan for the future
  clean-room repository's release; applies only there, not to this repository.
- [GNN Sparsification Budget](docs/gnn-sparsification-budget.md) —
  practitioner-facing usage note for the certified edge-sampling budget,
  with the `matrix_bernstein` trust caveat stated first.
- [Agentic Architecture Review](docs/arch/scaffold-agentic-architecture-review.md) — control-plane audit; live unattended `--commit` is B because Sequence 0 is unimplemented (verify/commit mismatch, mutable verifier, incomplete ladder, no host time budget). Planning contract A−; A+ not earned.
- [Commit Steward Protocol](docs/arch/commit-steward-protocol.md) — the
  verify-and-commit procedure that sits between the autonomous agent
  (which has no git authority) and `main`. The steward may veto; git
  stays in the host and is never authorized by a model verdict.
- [Contributing](governance/CONTRIBUTING.md) — contribution and review workflow.

## License

Apache 2.0. See [LICENSE](LICENSE).
