# Cluster Projector — the Set-Valued Spectral Projector and Its Davis–Kahan Pair

**Status:** COMPLETE — Steps 0+1 delivered in one run (2026-08-24, run
`20260824T161014Z-run-1`); see the delivery record below  
**Proposed:** 2026-08-24, run `20260824T161014Z-run-1`  
**Axis:** Perturbation bridge (ring 2) consuming the SGT center's
eigenbasis layer (ring 1)  
**Backlog relation:** the recorded follow-on of
`band-davis-kahan-cluster.md` and `band-davis-kahan-symmetric.md`
("a set-valued (non-interval) cluster projector would leave the band
interface entirely and needs its own definition + proposal"), i.e. the
completing slice of backlog item 9's difference family.

## The gap

Every projector on the shelf selects eigenvalues by an *interval*:
`spectralProjector` at `≤ c`, `bandProjector` at `(a, b]`. The classical
statements this family serves — Yu–Wang–Samworth Theorem 1, Davis–Kahan's
spectral-projector theorem — are stated at **clusters**: arbitrary sets
`U` of eigenvalues, with `P_U` the projector onto the span of the
eigenvectors whose eigenvalues lie in `U`. The delivered cluster-form
theorem reaches that generality in *spirit* (its pairwise δ is the
YWS-literal one) but its objects are still windows: a consumer wanting
the projector onto, say, `{λ : |λ| ≥ 3}` — two half-lines, not an
interval — has no object to name, and the band family cannot express the
subspace at all.

## Step 0 — the worked route (surveyed this run, before any statement)

**The definition.** The eigenbasis of `Spectral.lean` already supports
membership-filtered sums — `spectralProjector` is one, at `λ ≤ c`. The
set-valued projector is the same sum at an arbitrary `S : Set ℝ`:

```
clusterProjector M hM S = ∑_{i : λ i ∈ S} vᵢ vᵢᵀ
```

(`Finset.univ.filter (· → eigvalOf ∈ S)`, classical decidability; the
definition is `noncomputable` but **junk-free** — unlike `bandProjector`
there is no reversed-endpoint regime, since a set has no orientation.
This is a deliberate interface improvement recorded here: every
band-projector lemma that needed an `a ≤ b` guard needs none at sets.)

**The interface transfers through one lemma.** The entire delivered
band/perturbation machinery consumes the projector through the component
action `v i ⬝ᵥ (P *ᵥ y) = χ(sel i) · (v i ⬝ᵥ y)` (PolyFilter's
`eigvecOf_dotProduct_bandProjector_mulVec` is the engine's only projector
input). The set-valued twin `v i ⬝ᵥ (P_S *ᵥ y) = χ(λ i ∈ S) · (v i ⬝ᵥ y)`
therefore unlocks verbatim re-runs of:

- symmetry, idempotence, eigenbasis action (in-`S` modes fixed,
  out-of-`S` annihilated), contractivity, the Parseval expansion;
- the **product law through intersections**
  `P_S * P_T = P_{S ∩ T}` (the spectralProjector nestedness law's set
  twin; idempotence is its diagonal, disjoint-set orthogonality its
  empty-intersection case);
- the **complement law** `P_{Sᶜ} = 1 − P_S` (a `Finset.filter`/
  `filter_not` partition of the eigenbasis — *unavailable* to the band
  family, where `1 − bandProjector` is not a band projector; this is why
  the window difference form needed a separate complement engine and the
  set form does not);
- the trace/rank supplier (rank = cardinality of the in-`S` eigenbasis
  filter, the exact `{0,1}`-spectrum route of `rank_bandProjector_eq_card`).

**The Davis–Kahan pair at sets.** With the component action in hand, the
commutator/shift engine (F1 compression, range invariance, F2 expansion,
contractivity, the r-cancelling assembly) re-runs with `χ(a < λ ≤ b)`
replaced by `χ(λ ∈ S)`; the hypotheses become *membership* statements:

```
hnear : ∀ i, λᵢ ∈ S → |λᵢ − c| ≤ r          -- A's cluster within r of c
hfar  : ∀ j, μⱼ ∈ T → r + δ ≤ |μⱼ − c|       -- B's cluster δ-far outside
⇒ ‖P_B(T) * P_A(S)‖ ≤ ‖A − B‖ / δ                    (product form)

hrank + hnear + hfar-at-complement
⇒ ‖P_A(S) − P_B(T)‖ ≤ ‖A − B‖ / δ                    (difference form)
```

The difference form needs **no dichotomy and no interior case**: the
equal-rank identity reduces to `‖(1 − Q_T) P_S‖`, the complement law
rewrites `1 − Q_T = Q_{Tᶜ}` (the engine's own shape), and the product
form applies at `Tᶜ`. This is strictly simpler than the window cluster
form, whose interior/boundary dichotomy existed *only* because
`1 − bandProjector` is not a band projector.

**The honestly-blocked follow-on (recorded, not attempted).** The
YWS-literal *pairwise* set shape (one-sided separation between the
clusters' spectra, no center/radius) does **not** transfer: the window
proof's interior case consumed "every A-eigenvalue outside the window
lies outside the cluster range", which is false for sets — an
out-of-`S` A-eigenvalue can sit inside `S`'s range, in a gap, where the
projector-free expansion `δ ≤ ‖A − B‖` (which needs δ-farness from A's
*whole* spectrum) is unavailable, and the configuration is not trivial
(neither projector sees the gap eigenvalue). Whether the pairwise set
shape is true at all is open to this repo; it needs a different route
(eigenvalue-flow/Weyl tracking), not this engine. The center/radius
hypotheses below are the honest statement of what the algebraic engine
actually consumes — the module's existing `hnear`/`hfar` idiom, stated
between the clusters as sets.

**Statement-shape decisions, recorded before stating:**

1. `S : Set ℝ` (not a predicate `ℝ → Prop`): clusters are sets in the
   cited statements, and the complement law reads `Sᶜ`.
2. No `S.Finite` hypothesis anywhere: the filter is over `V` (finite),
   so `S` only ever enters through membership of finitely many
   eigenvalues — infinite `S` is harmless and the junk-free definition
   needs no guard.
3. The difference form keeps the equal-rank hypothesis (the identity's
   requirement, checkable through the rank supplier); the two-sided
   rank-free constant-2 symmetric form is a follow-on composition, not
   re-derived here.
4. The band agreement `clusterProjector M hM (Set.Ioc a b)
   = bandProjector M hM a b` is a public theorem, making the entire
   delivered band family the interval-set special case — the
   load-bearing bridge QA transports through.

## Step 1 — deliverable

1. New `Scaffold.Mathlib/GraphTheory/ClusterProjector.lean` (namespace
   `SpectralGraphTheory`; imports Spectral + Band; no new axiom): the
   definition and the interface lemmas above — symmetric, idempotent,
   the intersection product law, mode-selection action (both
   directions), the component action, commutation with `M`, the
   complement/partition pair, empty-set zero / covering-set one, the
   trace/rank supplier, and the band agreement.
2. New `SetForm` sections of `Perturbation/BandDavisKahan.lean` (+1
   import: ClusterProjector; no umbrella change needed beyond the new
   module's own import): the private engine at sets (F1, range
   invariance, F2, contractivity, core) and the two public theorems at
   exactly the Step-0 shapes.
3. QA `Scaffold/QA/Perturbation/ClusterProjector_QA.lean`, four
   sections: (a) the **non-interval witness** — on `diag(0, 5, 11)`,
   `P_{ {0, 11} } = diag(1, 0, 1)` pinned entrywise through the in-file
   Fin 3 diagonal spectral layer (a subspace no window expresses; the
   payoff object), with in-`S`/out-of-`S` action, complement-law, and
   rank pins; (b) the **band-agreement transport** — the set mirror of a
   window whose projector the delivered QA pinned, joined through the
   public agreement lemma (the bridge load-bearing); (c) **theorem
   instances** — the non-interval difference witness
   `S = {0, 11}` vs `T = {2, 4}` on `diag(0, 5, 11)` vs `diag(−1, 2, 4)`
   (both projectors diagonal-pinned, raw norm exactly `1`, bound `≤ 7`
   at exact-fit `c, r, δ`) and the ε = 0 attainment; (d) the **fence** —
   `hfar` isolated and refuted in proved form on the interior-gap
   configuration `A = B = diag(0, 5, 11)`, `S = {0, 11}`,
   `T = {5, 11}` (ranks equal, `hnear` verified, the out-of-`T`
   eigenvalue `0` at range-interior distance — the very configuration
   the recorded obstruction names, exercised as a hypothesis fence).
4. Records: this document, `proposals/README.md` (High row at start,
   Delivered row at end), README (module table + status), radar QA axis
   sync, scoreboard, `index/map/perturbation.md` +
   `index/map/spectral_graph_theory.md` (as shelf structure dictates),
   `index/sources/davis_kahan_1970.md` (the set-form mapping row), the
   umbrella `Scaffold.lean`, the execution plan, and the activity log.

Zero new axioms; every new declaration `#print axioms`-clean at the
standard three.

## Leverage

- Repairs an interface blind spot at the exact point the delivered
  family's own recorded follow-on names: the subspace a consumer of the
  cluster Davis–Kahan shape actually wants (non-interval clusters) had
  no object.
- Load-bearing by the falsifiability test: the engine re-run consumes
  the new definition's component action *exactly* — a misstated filter,
  complement law, or agreement bridge breaks the theorems or their QA
  loudly (the QA fence and the entrywise non-interval pin are engineered
  to knock the definition over if it is wrong).
- The complement law is a *simplification* of the trust-free crust: the
  window difference form's separate complement engine (6 private
  lemmas) is superseded at sets by one definition-level law.
- One definition + interface + two theorems + QA: the smallest coherent
  unit that makes the band family's interval constraint disappear.

## Delivery record (2026-08-24, run `20260824T161014Z-run-1`)

Delivered at exactly the committed shape. The new
`Scaffold/Mathlib/GraphTheory/ClusterProjector.lean` (namespace
`SpectralGraphTheory`; minimal imports Spectral + Band; the umbrella
importing it) and the new `SetForm` sections of
`Perturbation/BandDavisKahan.lean` (+1 import: ClusterProjector). Zero
new axioms (count stays 9; `#print axioms` via `wip/cp_axcheck.lean` on
all 18 public module declarations + both set-form theorems + all 27
public QA declarations: `propext, Classical.choice, Quot.sound` only,
every one). QA 1925 → 1953 (`ClusterProjector_QA` a new
Perturbation-domain file at 28).

- **The delivered interface.** All Step-1 items landed: the definition
  (classical decidability, junk-free), symmetry, the **intersection
  product law** `clusterProjector_mul_clusterProjector` (proved by the
  *action* route — the component action plus basis injectivity and the
  column-extraction idiom, not the entrywise expansion: shorter than
  the band nestedness proof and load-bearing on the component action
  itself), idempotence, the degenerate zero/one corners, disjoint-set
  orthogonality, mode selection (the full ite-action plus both
  specializations), the component action, the **complement pair**
  (`clusterProjector_add_clusterProjector_compl` by the action route;
  `one_sub_clusterProjector` immediate), commutation, capture equality
  at sets, the **band agreement** (the union/disjoint split done at the
  indicator level), and the trace/rank supplier (the
  `rank_bandProjector_eq_card` route with a private copy of the exact
  `{0,1}`-spectrum fact).

- **The engine re-run.** The SetForm sections mirror the window engine
  (F1 compression, range invariance, F2 expansion, contractivity,
  comm-shift, the r-cancelling core assembly) with the membership
  filter in place of the window indicator; the difference form is
  exactly the committed two-step composition (equal-rank identity →
  complement law → product form at `Tᶜ`) — **no dichotomy, no interior
  case**, the window form's separate six-lemma complement engine
  replaced by one definition-level law, as the proposal promised.

- **Pin techniques (the recurring fixes, this run's list).**
  Filter-instance hygiene dominated: `Finset.filter` at a set-membership
  predicate elaborates under *different* `DecidablePred` instances in
  definition-unfolded goals versus `classical`-tactic proofs, so `rw`
  with filter equalities stated in proofs fails on definition-unfolded
  filters even when displays match — the durable fix is to keep
  projector proofs in the *action/component* idiom (never rewriting
  filters) and to derive count pins from the trace lemma's own filter
  term rather than restating it (`exact_mod_cast h.symm`, never a
  hand-stated `have` about `.card`). `open Classical in` must precede
  the doc comment, not sit between doc and declaration. `Set.mem_Ioc` /
  `Set.mem_compl_iff` / `Set.mem_inter_iff` at this pin take explicit
  arguments, defeating dot-projection — use defeq `show` terms or
  `Set.mem_inter h₁ h₂` forward forms; membership in `S ∩ T` and `Sᶜ`
  are definitionally the conjunction/negation, so `hc.1` and
  `fun hc => hc h` typecheck directly. QA-side: `simp`'s normNum
  extension fails on *negative* real literals (`-1 = 5` survives simp;
  `abs` goals survive norm_num) — close those with `linarith` on the
  hypothesis, explicit `abs_le`/`le_abs` with `Or.inl`/`Or.inr` chosen
  by the sign of the case, and `simp` (which decides Fin-index `ite`s)
  before `norm_num`, never `norm_num` alone on entrywise matrix goals.

- **QA delivered at the four mandated sections** (28 declarations): (1)
  the non-interval witness — `P_{{0,11}} = diag(1,0,1)` on the imported
  `clusterA` fixture through the four-lemma composition (capture at
  sets to `({5}ᶜ)`, the complement partition, the singleton pin
  `P_{{5}} = diag(0,1,0)` via capture → band agreement → the two
  threshold pins, one of which (`spA_four`) is this file's single new
  entrywise pin through a copied private Fin 3 diagonal layer); the
  idempotence/action/disjointness instantiations and the four rank
  counts (2/1/2/2) through the trace route; (2) the non-interval
  difference instance on the new fixture `bm = diag(−1,5,11)` at
  exact-fit `c = 11/2, r = 11/2, δ = 1` — the theorem bound `≤
  ‖A−B‖/1 ≤ 1` (the norm via the max-abs-eigenvalue bridge at the
  diagonal difference) joined with the raw lower `1 ≤ ‖P−Q‖` at `e₀`
  (both projectors and the difference pinned entrywise); (3) the ε = 0
  attainment at `S = T = {5}` with the out-of-`T` separation genuinely
  discharged (distances 5 and 6 at δ = 1/2), the conclusion `‖P−P‖ ≤ 0`
  attained; (4) the `hfar` fence on the interior-gap configuration —
  ranks 2 = 2 through the counts, `hnear` verified, the out-of-`T`
  eigenvalue `0` at interior distance `11/2 < 11/2 + 1/2` (`hfar`
  refuted exactly there), and the hypothesis-free conclusion `‖P−Q‖ ≤
  ‖A−A‖/(1/2) = 0` refuted at norm ≥ 1 — the proposal's recorded
  obstruction exercised as a fence, with
  `cpQA_fence_only_hfar_fails` collecting the isolation.

- **Verification.** `lake env lean` on all three changed/new modules —
  zero errors, zero warnings each (after building ClusterProjector's
  olean first: `lake env lean` reads oleans for imports); explicit
  `lake build` targets all ✔ (2010/2010, 2193/2193, 2198/2198);
  `#print axioms` via `wip/cp_axcheck.lean` on all 47 accessible
  declarations — the standard three only; **full `lake build` ✔
  (2261 targets, "Build completed successfully"; zero warnings in the
  changed modules — the log's remaining diagnostics are the documented
  pre-existing set in untouched modules plus upstream Mathlib
  package notes)**; `lint_axioms` (**9**, unchanged), `check_citations`,
  `check_markdown_links` pass; scoreboard regenerated (**1953/9/0**,
  idempotent by md5). Records updated: this document,
  `proposals/README.md` (the Delivered row; the progress paragraph —
  the Active table empty again), README (1953; the cluster-projector
  module-table row; the Perturbation row's set-form sentence), the
  radar (QA axis synced 1925/49 → 1953/50, held 4.0), the scoreboard
  (all four verification rows + a new interpretation bullet),
  `index/map/spectral_graph.md` (the module-list line + the new
  section), `index/map/perturbation.md` (the set-form section + 2
  declaration rows), `index/sources/davis_kahan_1970.md` (the set-form
  mapping row), the umbrella `Scaffold.lean`, `docs/EXECUTION_PLAN.md`,
  and `docs/AGENT_ACTIVITY.md`. Nothing committed; the prior runs'
  deliveries preserved untouched.

- **Open follow-ons.** The YWS-literal *pairwise* set shape (no
  center/radius) remains honestly blocked as recorded in Step 0 — an
  out-of-`S` A-eigenvalue can sit inside `S`'s range, killing both the
  interior-case trivial regime and the direct engine route; a proof
  needs eigenvalue-flow/Weyl-tracking machinery, and whether the shape
  is true at all is open to this repo. The two-sided rank-free
  constant-2 *set* form composes from the delivered pair (equal-rank
  dropped via the symmetric form's both-orders trick) but was not
  re-derived here. The YWS/Davis–Kahan locators carry the standing
  verify-against-physical-copy caveat.
