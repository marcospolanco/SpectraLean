# Proposal: The Erdős–Rényi Random Graph as a Named Model

**Status:** Proposed. Prompted by an external repo observer's assessment
(relayed by the operator, 2026-09-05) that random-graph spectral theory
is a real gap in this project relative to its own stated scope, not a
deliberate deferral like the Matrix-Tree theorem. Authorizes no Lean,
axiom, or documentation change on its own.

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources on random
graph theory (Bollobás, *Random Graphs*; Chung & Lu on spectra of
random graphs). Do not copy this proposal verbatim or consult
quarantined materials.

## The claim this document is answering

Not "should this project build full `G(n,p)` spectral theory" — that
is a large literature (semicircle law, sharp spectral-gap
concentration, connectivity thresholds) and not a one-proposal
undertaking. The narrower, actionable question: **does this project
have a real, honest first slice available now, and how cheap is it
given what already exists on the shelf?** The answer to the second
half is the actual finding here: cheaper than it looks, because the
core probabilistic machinery already exists for an unrelated reason
and has never been recognized as an instance of this model.

## Why this gap is different from the others already on record

Two other "why doesn't this exist" gaps are already on record in this
project's own documents, and both have a considered answer:
[`weighted-matrix-tree-theorem.md`](weighted-matrix-tree-theorem.md)
is explicitly gated by `docs/6_SGT_BACKLOG.md` item 7 pending a named
consumer, and the log-Sobolev inequality's consumer gate was
discharged 2026-09-01 (`docs/7_SGT_RADAR.md`) — adopting one is a
recorded operator decision away, not a missing-machinery gap.

Random graph models have neither kind of paper trail. Checked
directly: the string "random graph" (any capitalization/hyphenation)
appears in exactly two places in this entire repository — the
one-line charter of `docs/7_SGT_RADAR.md`'s axis 7 ("Perturbation,
randomness, and algorithms — matrix concentration, **random graphs**,
stability, and numerical/spectral algorithms") and a citation title in
`docs/4_PARTNERSHIPS.md`'s research-landscape survey. No backlog item,
no proposal, no gate, no cost estimate — a charter promise with zero
follow-through, not a considered deferral. That is the actual gap this
document closes: not "build `G(n,p)` theory" but "give this axis the
same honest survey-and-price treatment every other candidate gets
before anyone decides whether to adopt it."

## What Mathlib provides

**Verified absent.** Repository-wide and pinned-Mathlib-wide search for
`erdosRenyi`, `ErdosRenyi`, `randomGraph`, `RandomGraph` (any casing):
zero hits anywhere, including in the pinned Mathlib itself. No random
graph model exists at any layer this project could import instead of
building.

## What's already on the shelf — the actual finding

`Scaffold/Mathlib/GraphTheory/EdgePerturbation.lean`'s `perturbWeight`
(line 378) is generic in a base graph `A : WAdj` and a per-edge
inclusion probability `p : (V × V) → ℝ`:

```
def perturbWeight (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (ω : (V × V) → Bool) : Matrix V V ℝ :=
  ∑ e : V × V, perturbAdj A p e ω
```

where `perturbAdj A p e ω = ((if ω e then 1 else 0) - p e) • edgeAdj
e.1 e.2 (A e.1 e.2)` — the **centered** (mean-zero) random weight on
edge `e`. This was built for a completely different purpose (Fiedler-
subspace stability under small random perturbation of a fixed graph),
and its existing consumers all read `A` as "the base graph being
perturbed" — small, sparse, structurally meaningful.

Nothing in the definition requires that reading. Instantiate `A` at
the **complete graph** (weight `1` off the diagonal, `0` on it — not
yet defined anywhere in this repository, a one-line gap) and `p` at a
**constant** `p e = p`: `perturbWeight (completeAdj) (fun _ => p)` is
then, by construction, **exactly the centered adjacency matrix of
`G(n,p)`** — the object the actual G(n,p) spectral literature studies
directly (Füredi–Komlós and every matrix-concentration-based spectral
gap argument for random graphs works with `A - 𝔼[A]`, precisely this
object, not the raw `{0,1}`-valued adjacency matrix). This is not a
loose analogy; it is the same mathematical object under a
specialization of already-general parameters.

Two existing generic theorems then apply with **zero new inequality
content**, only concrete instantiation:

- **`edgePerturbation_norm_tail`** (`Derived/EdgePerturbationTail.lean:232`):
  a matrix-Hoeffding operator-norm tail bound on `‖perturbWeight A p
  ω‖`, generic in `A` and `p`. At `A = completeAdj`, `p` constant, this
  is already a concentration bound for `G(n,p)`'s centered spectral
  norm — the deterministic proof is untouched; only the variance-proxy
  term `‖∑ₑ perturbEdgeLap A e · perturbEdgeLap A e‖` needs computing
  concretely for the complete-graph fixture.
- **`edgePerturbation_degree_tail_bernstein`** (`Derived/EdgePerturbationTail.lean:1013`):
  a Bernstein tail on `deg (A + perturbWeight A p ω) v - deg A v`,
  generic in `A` and `p`. At the same specialization this is degree
  concentration around `(n-1)p` — the actual classical first fact
  about `G(n,p)` (every vertex's degree is `\text{Binomial}(n-1,p)`,
  concentrated), already provable from the shelf as it stands. (The
  project's own README already lists "Vertex-Degree Concentration" as
  a delivered result built on this exact engine — it is already a
  `G(n,p)` fact, simply never named as one.)

## Scope decision: package and specialize, don't re-derive

Given the above, this proposal's build order is deliberately not "port
a random-graph textbook into Lean." It is: name the model, specialize
the two theorems above to it, and compute the concrete constants that
specialization requires — the same shape of cheap-because-surveyed
finding `mutual-information-and-data-processing.md` made for its own
axis, not a from-scratch proof engine.

## Build order

### Step 0: Survey (this document)

Done above. Recorded finding: the centered-adjacency-matrix object and
its two tail bounds already exist generically; only the complete-graph
base and the concrete constant computation are missing.

### Step 1: The model itself

```
def completeAdj (V : Type*) [Fintype V] [DecidableEq V] : WAdj (V := V) :=
  fun i j => if i = j then 0 else 1

noncomputable def erdosRenyiWeight (V : Type*) [Fintype V] [DecidableEq V]
    (p : ℝ) (ω : (V × V) → Bool) : Matrix V V ℝ :=
  completeAdj V + perturbWeight (completeAdj V) (fun _ => p) ω
```

`erdosRenyiWeight` is the **raw** (uncentered) object most informal
usage of "the random graph `G(n,p)`" means; `perturbWeight
(completeAdj V) (fun _ => p)` alone is the **centered** object the
concentration theorems below actually consume. Both should be named,
since a downstream reader expects "the random graph" to be the
`{0,1}`-ish object, not its deviation from the mean. QA a hand-verified
small case immediately (`Fin 2`/`Fin 3`, enumerate the finitely many
outcomes) before anything else, per this project's standing practice
for a new definition.

### Step 2: Degree concentration, named

Specialize `edgePerturbation_degree_tail_bernstein` at `A =
completeAdj V`, `p` constant, computing `degPerturbWeight
(completeAdj V) v e` and its bound `M` concretely for this fixture
(mechanical: every off-diagonal entry is `1`, so the per-edge deviation
bound is a fixed constant independent of `v`). State the corollary in
`G(n,p)`-native language: `deg(G) v` concentrates around `(n-1)p` at a
Bernstein rate. Zero new axioms; this is packaging plus a concrete
constant computation, not new proof machinery.

### Step 3: Spectral-norm concentration, named — honestly scoped

Specialize `edgePerturbation_norm_tail` the same way. The real work
here is computing `‖∑ₑ perturbEdgeLap (completeAdj V) e · perturbEdgeLap
(completeAdj V) e‖` concretely for the complete-graph fixture — this
scales with `n` and is the step most likely to need real Lean effort
(a sum over all `n(n-1)` ordered edge pairs, not a single algebraic
identity). **Honest scope note, stated up front rather than
discovered late:** the resulting bound is whatever generic matrix
Hoeffding gives at this specialization — it is **not** claimed to
match the sharp classical constant from the trace-moment literature
(Füredi–Komlós's `O(√(np))`, versus the typically-looser
`O(√(np log n))` a generic matrix-concentration route tends to give).
State the actual derived bound plainly and let it be what it is,
matching this project's own standing practice of reporting inflated
or non-sharp constants honestly (e.g. the plain-walk spectral
certificate's own "conservative at both ends" note) rather than
implying a tightness that was not proved.

### Deferred and removed

- **Sharp spectral-gap concentration** (Füredi–Komlós, Feige–Ofek, or
  any trace-moment-method route to the classical tight constant) — a
  genuinely different, harder proof technique from anything on this
  project's shelf; a separate proposal if ever pursued, not attempted
  here.
- **The semicircle law / empirical spectral distribution** — measure-
  theoretic machinery (weak convergence of empirical spectral
  measures) this project does not currently have reason to build;
  out of scope.
- **Connectivity threshold** (`p > \log n / n` almost sure
  connectivity) — a genuinely different argument (first/second moment
  method on component structure, not concentration of a fixed
  statistic); not attempted here.
- **The configuration model** — a different, harder-to-specify random
  graph model (fixed degree sequence, uniform random matching of
  half-edges) with no natural specialization of `perturbWeight`; a
  separate proposal, not a corollary of this one.
- **Sparse-regime refinements** (`p = c/n` for constant `c`, where
  concentration bounds of the shape derived here become vacuous or
  need a different normalization) — worth flagging honestly as a real
  limitation of the generic-matrix-concentration route, not
  papered over.

## What Mathlib might yet provide that changes this costing

Not surveyed exhaustively for this document (unlike `weighted-matrix-tree-theorem.md`'s
deeper dive) — a targeted search for `Mathlib.Probability.Independence`-adjacent
combinatorial/random-graph material, and for any existing binomial or
Bernoulli-sum concentration this project's own `bernPMF`/`BernoulliProduct.lean`
layer might already generalize, should be Step 0's actual first action
for whoever picks this up, before Step 1 lands anything.

## QA plan

- `completeAdj`/`erdosRenyiWeight` positive witnesses: `Fin 2` and
  `Fin 3`, every outcome enumerated by hand (the outcome space is
  finite and small — `2^(n(n-1)/2)` symmetric edge choices), cross-
  checked against the definition directly.
- Degree-concentration corollary: instantiate at a small `n`, `p`
  fixture and confirm the displayed Bernstein bound is non-vacuous
  (a real, checkable numeric threshold, not a bound that only holds
  vacuously at the fixture's scale) — this project's standing
  adversarial-fence discipline (`governance/ADVERSARIAL_REVIEW.md`)
  applies from delivery, not as a later audit pass.
- Norm-concentration corollary: same non-vacuity check, plus an
  explicit numeric comparison against the naive union-bound degree
  argument, to make the "not sharp" scope note in Step 3 a checked
  fact rather than an assertion.

## Gate — this needs an operator decision, not routine backlog treatment

Same shape as `weighted-matrix-tree-theorem.md` and
`mutual-information-and-data-processing.md`: no backlog item or
proposal currently names a `G(n,p)` consumer as a blocking dependency.
This document's case for adoption is that axis 7's own charter already
promises this territory and nothing has ever priced it — a real but
different kind of case than "X is blocked," and the cheapest to act on
of the three current charter-gap candidates because Steps 2–3 reuse
already-proved inequalities rather than requiring new ones. An
autonomous run should not begin Step 1 without this decision recorded
here as adopted, or a different named consumer supplied.

## Operating instructions for an autonomous run

*(Apply only after the Gate above is resolved.)*

- One step per run; Step 3's concrete-constant computation is the one
  likely to need more than one, per this project's own precedent for
  "the step that needs a real sum over a scale-dependent fixture."
- **No new axioms.** Everything surveyed above stays inside already-
  proved `EdgePerturbation`/`EdgePerturbationTail` machinery plus
  concrete arithmetic; if Step 3 turns out to need something genuinely
  absent (e.g., a sharper concentration inequality this project does
  not have), stop and record the precise obstruction rather than
  admitting anything.
- State the "not the sharp classical constant" scope note in the
  delivered docstring itself, not only in this proposal — a reader of
  the theorem statement should not have to find this document to learn
  the bound is generic-route, not literature-sharp.
- Do not fold this into `EdgePerturbation`'s own delivery record or
  treat it as extending that program; this is new packaging of
  existing machinery for a different named purpose (closing axis 7's
  charter gap), not a missing piece of the edge-perturbation drift
  program.

## Open next step

Blocked on the Gate above, not on any technical prerequisite. Step 0's
Mathlib re-survey (the "What Mathlib might yet provide" section above)
could be done at any time at no cost; Step 1 should wait for an
explicit adoption decision, or a different named consumer, per this
project's standing "no new machinery ahead of a decision" norm.
