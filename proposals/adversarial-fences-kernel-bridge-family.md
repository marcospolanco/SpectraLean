# The Kernel-Bridge Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-04 by run `20260904T141530Z-run-1`,
session `ses_f9339f4e0ffeTK4EVFefO84ern`; see the delivery record).

## Scope

The prior terminal handoff's named next target: "`KernelBridge_QA`
(the smallest remainder) and then the `ResistanceMetric` consumer set
— after which the electrical cluster's falsification surface is
complete." This run audits the kernel-equality bridge family:
`Scaffold/Mathlib/GraphTheory/SimpleGraphAdapter.lean`'s Bridge section
(`ker_laplacian_eq_ker_supportGraph_lapMatrix`,
`finrank_ker_laplacian_eq_card_supportGraph_components`,
`laplacian_ker_basis`, `laplacian_ker_basis_apply`) plus the weighted
center characterization chain it consumes (`Spectral.lean`'s
`laplacian_mulVec_eq_zero_iff_forall_reachable` and both of its halves,
`eq_of_supportGraph_walk` and
`eq_of_laplacian_mulVec_eq_zero_of_pos_weight`, together with the
connected forms `exists_const_of_laplacian_mulVec_eq_zero`,
`laplacian_mulVec_eq_zero_iff_exists_const`,
`laplacian_kernel_eq_span_onesVec`). Its QA file
(`KernelBridge_QA.lean`, 240 lines, delivered with the 2026-08-18
electrical-structure re-sequencing) predates the adversarial-review
discipline and instantiates only **nonnegative** fixtures (the
three-vertex path and two disjoint edges, imported from
`Connectivity_QA`): no `hnonneg` clause of the family has a negative
witness anywhere in the repository, and no `hA` clause of the family
has ever been examined for fenceability.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(nine precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger, regular
Cheeger, effective-resistance, electrical-flow, Foster) — re-read every
theorem's hypothesis clauses, identify those with no negative witness,
and close each with a hypothesis-form fence (the dropped-hypothesis
statement refuted at a fixture where every other hypothesis is
genuine, certified by an isolation companion), or record a
non-fenceable with its mechanism.

Consumer set (the leverage case): the center characterization chain is
the most-consumed kernel API on the shelf — `Electrical.lean` consumes
`laplacian_mulVec_eq_zero_iff_forall_reachable` at its solvability
hinge and `eq_of_supportGraph_walk` at its confinement layer;
`Fiedler.lean` (×3), `Heat.lean` (×2), `Foster.lean` (×3), and
`Mixing.lean` consume `laplacian_kernel_eq_span_onesVec`; the bridge
itself feeds every electrical QA family the cluster's audits have been
consuming in order.

## Step-0 findings: the priced fence list

Twelve fences at three new fixtures, all `Fin 2`/`Fin 3` (matrix
literals evaluate at those scales). No delivered fixture serves: the
existing corpus's signed fixtures either have disconnected support
(`Signed_QA`'s `sgNegA`: its support is the single edge `0—1` with
vertex `2` isolated, so the `hconn`-carrying clauses cannot be priced
there) or are normalized-operator fixtures with no raw-kernel pins
(`Cheeger_QA`'s `rcSAdj`). The co-hypothesis discipline from the
regular-Cheeger audit applies in full: **`hconn` is a co-hypothesis of
`laplacian_kernel_eq_span_onesVec` and the exists-const forms, so
their `hnonneg` fences require a signed fixture whose support is
genuinely connected** — the survey's decisive pricing constraint.

### The fixtures

- **`kbfNegEdge2Adj` (Fin 2):** `!![0, -1; -1, 0]]` — symmetric, one
  negative edge, no positive entry anywhere, so the support graph is
  edgeless (two components, `lapMatrix = 0`, RHS kernel = ⊤). The
  weighted Laplacian is `[[−1, 1], [1, −1]]`: kernel exactly the
  constants (`f 0 = f 1`), by the row equation.
- **`kbfSgnPath3Adj` (Fin 3):** `!![0, 2, -1; 2, 0, 2; -1, 2, 0]]` —
  symmetric, support the path `0—1—2` (the `2`-entries) with the
  negative edge `(0,2)` dropped by the support construction:
  **connected support, signed weights**. The Laplacian is
  `[[1, −2, 1], [−2, 4, −2], [1, −2, 1]]` (rows 1 and 2 are multiples
  of row 0), whose kernel is the plane `f 0 − 2 f 1 + f 2 = 0`,
  containing both `1` and the nonconstant `![1, 2, 3]`.
- **`kbfAsymSinkAdj` (Fin 3):** `!![0, 1, 1; 0, 0, 0; 0, 0, 0]]` —
  **asymmetric, nonnegative** (every `hnonneg` clause genuine), one
  source vertex `0` pointing at the sinks `1, 2`. The Laplacian is
  `[[2, −1, −1], [0, 0, 0], [0, 0, 0]]`: the sink rows are vacuous,
  so the kernel is the plane `2 f 0 = f 1 + f 2`, containing the
  nonconstant `![1, 2, 0]`.

### Priced fences

**Group α (`kbfNegEdge2Adj`, support edgeless):**

1. `laplacian_mulVec_eq_zero_iff_forall_reachable` (`hnonneg`, the ←
   direction): at `f = ![1, 0]` the RHS is junk-trivially true
   (edgeless support → `Reachable i j → i = j`), while
   `L *ᵥ ![1, 0] = ![−1, 1] ≠ 0` — the dropped-hnonneg iff is false.
2. `laplacian_mulVec_eq_zero_of_forall_reachable` (`hnonneg`): the
   same witness refutes the implication directly.
3. `ker_laplacian_eq_ker_supportGraph_lapMatrix` (`hnonneg`):
   `![1, 0]` lies in the RHS kernel (edgeless `lapMatrix = 0`) but not
   the LHS kernel — the kernels separate.
4. `finrank_ker_laplacian_eq_card_supportGraph_components`
   (`hnonneg`): `finrank ker L = 1` (the kernel is exactly
   `ℝ ∙ ![1, 1]`, via `finrank_span_singleton`) against `card
   components = 2` (the edgeless classification) — `1 ≠ 2`.

**Group β (`kbfSgnPath3Adj`, connected support, signed):**

5. `eq_of_laplacian_mulVec_eq_zero_of_pos_weight` (`hnonneg`, the
   mechanism level): `0 < A 0 1 = 2` genuine, `L *ᵥ ![1, 2, 3] = 0`
   genuine, yet `![1, 2, 3] 0 = 1 ≠ 2` — the termwise-vanishing step
   of the Dirichlet identity is exactly where nonnegativity enters.
6. `eq_of_supportGraph_walk` (`hnonneg`, the walk level): the same
   kernel vector with the explicit support walk `0 → 1`.
7. `laplacian_mulVec_eq_zero_iff_forall_reachable` (`hnonneg`, the →
   direction): LHS true at `![1, 2, 3]`, RHS false (`0` reaches `1`,
   `1 ≠ 2`) — the direction group α's witness cannot reach, showing
   the α fence is not an artifact of the edgeless corner.
8. `laplacian_kernel_eq_span_onesVec` (`hnonneg`; `hconn` genuine at
   the fixture): `![1, 2, 3]` is a kernel vector outside the constant
   line.
9. `laplacian_mulVec_eq_zero_iff_exists_const` and
   `exists_const_of_laplacian_mulVec_eq_zero` (`hnonneg`; `hconn`
   genuine): the same witness — a kernel vector that is not constant.
10. `ker_laplacian_eq_ker_supportGraph_lapMatrix` (`hnonneg`, second
    orientation): `![1, 2, 3]` lies in the *weighted* kernel but not
    the support graph's `lapMatrix` kernel (whose vectors are constant
    on the connected support) — the separation the other way from
    fence 3.
11. `finrank_ker_laplacian_eq_card_supportGraph_components`
    (`hnonneg`, second witness): `2 ≤ finrank ker L` (`1` and
    `![1, 2, 3]` are linearly independent kernel vectors) against
    `card components = 1` (connected) — `2 ≠ 1`.

**Group γ (`kbfAsymSinkAdj`, asymmetric, nonnegative):**

12. `eq_of_laplacian_mulVec_eq_zero_of_pos_weight` (`hA`): the
    family's only `supportGraph`-free statement — `hA` is proof
    -internal (consumed by `laplacian_quadForm`), so the
    dropped-`hA` statement is well-formed. At the sink star every
    other hypothesis is genuine (`hnonneg` holds entrywise, the
    kernel equation holds at `![1, 2, 0]`, `0 < A 0 1`), and the
    conclusion `f 0 = f 1` fails (`1 ≠ 2`): the symmetry hypothesis
    is load-bearing at the quadratic-form step, not merely at the
    `supportGraph` display.

### Recorded non-fenceables

- **The `hA` clauses of every `supportGraph`-carrying statement**
  (`ker_laplacian_eq_ker_supportGraph_lapMatrix`,
  `finrank_ker_laplacian_eq_card_supportGraph_components`, the iff and
  both walk-level halves, the basis interface): the display itself
  consumes `supportGraph A hA`, so the dropped-hyp statement does not
  elaborate — the statement-shape entanglement mechanism class
  (established in the effective-resistance audit).
- **The `hA`/`hnonneg`/`DecidableEq` clauses of `laplacian_ker_basis`
  and `laplacian_ker_basis_apply`:** consumed by the definition's own
  signature; only instantiable at genuine input. The basis's
  consumer-visible obligations (indicator values, spanning) are pinned
  by the existing positive QA at both fixtures.
- **The `hconn` clauses of the span form and exists-const forms:**
  already fenced by `Connectivity_QA`'s delivered disconnected
  witnesses (`connDisc_kernel_not_constants_QA`,
  `connDisc_kernel_exceeds_constants_QA`).
- **Degenerate corners** (`Fintype.card V = 0`, the one-vertex graph):
  screened — both sides of every statement compute to equal trivial
  values (kernel of the zero space = 0 = component count of the empty
  graph; one vertex gives `finrank 1 = card 1`); no junk separation
  exists.

## Delivery plan

QA-only, zero axiom contact (count stays 4; `#print axioms` audit on
every new declaration; no `-- @refutes` tags — theorem instantiations,
nothing admitted consumed). Spike first in
`wip/kbfences_spike.lean` to zero errors/zero warnings, then land as a
pure insertion — the `BridgeFences` section of
`Scaffold/QA/SpectralGraph/KernelBridge_QA.lean`. Full verification
ladder per the scoreboard's standard row.

## Delivery record

DELIVERED at the full priced scope — all 12 fences closed with
isolation companions as the `BridgeFences` section of
`KernelBridge_QA.lean` (a pure insertion, 558/0 in numstat plus the
Purpose-block sentence; spiked first in `wip/kbfences_spike.lean` to
zero errors/zero warnings, five fix rounds). QA 4817 → 4876 (+59 by
the generator metric; 65 declarations: 59 theorems + 6 `def`s — the
three fixtures `kbfNegEdge2Adj`/`kbfSgnPath3Adj`/`kbfAsymSinkAdj` and
the three walk witnesses `kbfSgn3_walk01`/`_walk10`/`_walk12`). Radar
QA axis synced to 4876, score held 4.5 per protocol (negative
witnesses of an already-counted family, not a named-gap closure).

Zero axiom contact: `#print axioms` via `wip/kbfences_axcheck.lean` on
all 65 new declarations — every one exactly `propext,
Classical.choice, Quot.sound`; no `-- @refutes` tags (theorem
instantiations, nothing admitted consumed). The fence shapes landed
exactly as priced: the group-α iff/←-half/bridge/dimension fences at
the edgeless-support negative edge (the kernel characterized exactly
as `ℝ ∙ ![1,1]` through the row equations, `finrank_span_singleton`
closing the count against the `Nat.card_eq_two_iff` edgeless
classification); the group-β mechanism/walk/iff-→/span/exists-const/
bridge/dimension fences at the connected signed path (the kernel
vector `![1,2,3]` pinned row-by-row through `laplacian_mulVec_apply`
and the fixture entry tables; the `≥ 2` dimension witness through
`LinearIndependent.pair_iff'` + `finrank_span_eq_card` +
`Submodule.finrank_mono`; the support-graph connectivity through
explicit center-anchored walks, keeping the `hconn` co-hypothesis
genuine); and the group-γ `hA` fence at the asymmetric nonnegative
sink star with the isolation packaged as conjuncts (entrywise
nonnegativity, the kernel equation, the positive pair — every other
hypothesis genuine).

**Technique findings** (from the spike's five fix rounds):

1. **`fin_cases` on a `Fin`-indexed hypothesis or goal leaves
   eta-wrapped literals** (`(fun i => i) ⟨0, ⋯⟩`) that defeat `rw`
   of `rfl`-proved entry lemmas — the pattern match fails on the
   wrapper even though the entries are definitionally the numerals.
   Two robust routes: `show` with the concrete index (defeq
   forgives the wrapper and evaluates the matrix literal), or an
   entry-*disjunction* lemma (`A i j = 0 ∨ A i j = -1`) proved by
   `fin_cases` + `rfl` that can then be `rcases`-ed at the
   un-normalized index. A sharpening of the recorded
   Fin-4-evaluation trap: even at Fin 2/3 it is the *index* wrapper,
   not the matrix scale, that breaks `rw`.
2. **`SimpleGraph.Walk` is data, not a proposition** — walk
   witnesses cannot be `theorem`s ("type of theorem is not a
   proposition"); they must be `def`s, and fences that need a walk
   state `Reachable` (the `Nonempty` proposition) witnessed by the
   def.
3. **`Walk.cons`'s named arguments bind the *final* endpoint at
   `w`** — `(u := 0) (v := 1) (w := 0)` builds a walk from `0` to
   `0` through `1`, and the resulting type mismatch surfaces as a
   misleading "invalid constructor ⟨…⟩, expected type must be an
   inductive type" on the *adjacency* anonymous constructor, far
   from the cause.
4. **`refine linearIndependent_pair ?_ ?_` strands the module type**
   (the stuck-`Module ?m ?m` error is reported at the theorem
   *statement*, not the refine) — and the pinned Mathlib's
   `linearIndependent_pair` is anyway about `Set`-coerced pairs; the
   `![x, y]`-shaped route is `LinearIndependent.pair_iff'`, rw-ed
   with the first component's nonzero proof supplied inline.
5. **Projection notation must not break across the line after the
   receiver's closing parenthesis** — `(supportGraph A hA)` newline
   `.lapMatrix_…` parses the parenthesized graph as a *function*
   ("function expected at … term has type SimpleGraph (Fin 2)");
   the robust shape is binding the lemma into a `have` with the
   receiver and projection on one line. Plus two smaller notes:
   `Submodule.span_le` yields goals in the set-coercion (`x ∈ ↑p`)
   where `LinearMap.mem_ker` will not `rw` — `show (f x = 0)`
   closes by defeq — and for equality-of-kernels fences the `rw
   [h]/[← h] at hmem` direction is fixed by which side's membership
   the witness already carries.

**Verification:** spike first (`wip/kbfences_spike.lean` — the full
65-declaration delivery, iterated to zero errors/zero warnings before
any shelf edit); `lake env lean` on the landed module (zero errors,
zero warnings); explicit `lake build
Scaffold.QA.SpectralGraph.KernelBridge_QA` ✔; the 65-declaration
axiom audit above; **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh
artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4
current axioms, unchanged; only the allowlisted-confirmed PF
finding); `check_refutation_independence` (9-tag clean — no tags
touched); `check_public_reachability` clean (63 repo modules);
`check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (**4876/4/0**) with the verification row;
map-freshness exit 0 after the 4817 → 4876 stats sync in both map
data files and SVG regeneration (49 stations, no status change —
none owed). The landing verified a pure insertion (558/0 in numstat,
plus the Purpose-block sentence). Records updated: this proposal
(COMPLETE + this delivery record), `proposals/README.md` (new
Delivered row), README (4876 + the electrical-structure row's
kernel-bridge-audit clause), the radar (QA axis synced, held 4.5),
`index/map/spectral_graph.md` (the fences paragraph in the
SimpleGraphAdapter section), the backlog item-2 falsification-surface
note, the scoreboard verification row, both map data tables +
regenerated SVG, the execution plan, and the activity log. Nothing
committed; the prior runs' committed state preserved.

**Remaining risk:** none owed by the delivery — QA-only, no axiom
disposition changed, no public statement changed. Honest scope: the
kernel-bridge family's falsification surface is complete; the
electrical cluster's one remaining QA family (the `ResistanceMetric`
consumer set beyond the already-delivered metric-residual fences) is
the method's next target, after which the electrical cluster's
falsification surface is complete and the method's next applications
move to the remaining pre-discipline QA families elsewhere (a fresh
Step-0 consumption survey should pick, per the standing handoff).
