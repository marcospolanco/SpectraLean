# Proposal: PageRank Distributions — the Second Perron–Frobenius Consumer

**Status:** **DELIVERED 2026-08-24** (run `20260824T045932Z-run-1`) —
Step 0 (this survey) and Step 1 (the module + QA) in one run per the
directed-operators/irreducible-stationary Steps 0+1 precedent; see the
delivery record at the bottom. Zero new axioms (count stays 9); the
three PageRank theorems are conditional on `perron_frobenius` exactly
as this document specified, the nine structural declarations
unconditional.

Assessed from `Scaffold/Mathlib/GraphTheory/IrreducibleStationary.lean`
(the delivered PF-consumer layer's exact statement shapes), the pin's
`Relation.ReflTransGen.single`, `Scaffold/Mathlib/GraphTheory/Normalized.lean`
(`walkTransitionMatrix`, `walkTransitionMatrix_row_sum`,
`walkTransitionMatrix_apply`), and `Spectral.lean` (`deg` = row sum,
`WAdj` an abbrev for `Matrix V V ℝ`).

## The obligation this discharges

`perron_frobenius` (admitted 2026-08-22) named two consumers; the first
(irreducible stationary distributions) was delivered 2026-08-24. This is
the second, and it is the one with content beyond the axiom's
application site: the irreducible-stationary layer requires `A.IsIrreducible`
as a hypothesis, but the walks that motivate PageRank — web graphs,
citation graphs — are *reducible*: their raw stationary distributions
are non-unique (the reducibility fence of `IrreducibleStationary_QA`
exhibits two on a two-block fixture). PageRank's teleportation
construction is exactly the repair: mixing `α • P` with the uniform
matrix `(1−α) • n⁻¹ • J` puts a positive floor in every entry, making
the mixed walk irreducible *unconditionally* — the reducibility of the
input is the point, not an obstruction. The deliverable is the
stationary theory of the mixed walk: existence, uniqueness among
nonnegative distributions, and full support — all conditional on
`perron_frobenius` through the delivered consumer layer, never
foundationally proved.

Load-bearing growth per the strategy's falsifiability test: the new
theorems consume `existsUnique_stationaryVec_of_irreducible`'s exact
statement shape at `M := googleMatrix A α` through a one-line bridge —
if that theorem (or the bridge, or the row-sum theorem feeding `hdeg`)
were misstated, the PageRank statements break loudly. This is the
second structural consumer of the axiom's clause chain, and the first
that exercises it on input the axiom layer itself would reject.

## The statement (Step-0 recorded shape)

For `A : WAdj (V := V)` nonnegative with positive out-degrees, `V`
nonempty, and `α ∈ [0, 1)`, writing `G = googleMatrix A α`:

1. **The construction (unconditional):**
   `G i j = α * P i j + (1 - α) * (card V)⁻¹` entry form;
   `0 < G i j` for every `i j` (the teleportation floor);
   `G.IsIrreducible` (every pair one step apart through the floor);
   `∑ j, G i j = 1` (row stochasticity — note: for *every* real `α`,
   since row stochasticity is affine; recorded below).
2. **Existence with full support** (conditional):
   `∃ π, (∀ i, 0 < π i) ∧ (∑ i, π i = 1) ∧ π ᵥ* G = π`.
3. **The `∃!` packaging** (conditional):
   `∃! π, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧ π ᵥ* G = π`
   — **with no irreducibility hypothesis on `A`**.
4. **Full support** (conditional): every nonzero nonnegative vector
   fixed by `G` is strictly positive.

Statement-shape decisions recorded before stating:

- **Carrier `WAdj`, entry-form definition** — the entry form
  `α * P i j + (1-α) * n⁻¹` (not the outer-product `v vᵀ` or scalar-smul
  form) because QA pins entries at literal indices and the floor
  inequality is read off entrywise.
- **`0 ≤ α ∧ α < 1`, not `0 < α < 1`.** At `α = 0` the matrix is
  `n⁻¹ • J`, strictly positive on nonempty `V`: the theorem is true and
  the uniform distribution is the unique stationary one, so excluding it
  would understate the statement. The conventional `0 < α` (Page–Brin
  use `0 < α < 1` with `1 − α ≈ 0.15`) is a modeling choice inside the
  proved range, not a hypothesis the mathematics needs. Both endpoints
  are fenced in QA exactly because the range is load-bearing: at
  `α = 1` (teleportation removed) uniqueness dies on reducible input,
  and at `α = −1` the mixed matrix degenerates (on `K₂` to the
  identity) and uniqueness dies with it.
- **Convention difference from the source recorded:** Page–Brin–Motwani–
  Winograd work with the *column*-stochastic web matrix and teleportation
  `E = v vᵀ` for a personalization vector `v`; this module states the
  transposed convention (row-stochastic walk, uniform teleportation),
  matching the shelf's `walkTransitionMatrix` row-stochasticity
  interface. The stationary vector of the row form is the left
  eigenvector at eigenvalue 1 = the PageRank vector of the column form
  at uniform personalization.
- **Nothing about power iteration, rates, or convergence.** Geometric
  convergence of the iteration `π_{t+1} = π_t ᵥ* G` needs strict
  spectral dominance, which the axiom deliberately does not claim (the
  `strict_dominance_refuted_QA` imprimitivity fence); mixing-rate
  statements on the directed axis stay gated on a primitivity-shaped
  admission, explicitly not smuggled in here.
- **The bridge is general:** `walkTransitionMatrix M = M` for any `M`
  with all row sums `1` is stated as its own unconditional theorem —
  any future row-stochastic consumer (not just the Google matrix) can
  compose the same way.

## Route (every dependency verified present)

1. **The floor:** `0 < G i j` from `α ≥ 0`, `P i j ≥ 0`
   (`walkTransitionMatrix_apply` + positive degrees), `1 - α > 0`, and
   `0 < (card V : ℝ)⁻¹` (`Fintype.card` positive on nonempty `V`).
2. **Irreducibility:** `ReflTransGen.single` of the floor at every pair
   — the support digraph is complete. `hex` falls out the same way.
3. **Row stochasticity:** `∑ j, G i j = α * ∑ j, P i j + (1-α) * (n * n⁻¹)
   = α + (1-α) = 1` (`walkTransitionMatrix_row_sum`, `Finset.sum_const`,
   `inv_mul_cancel₀` at `n ≠ 0`). Hence `deg G i = 1 > 0` supplies the
   consumer layer's `hdeg`.
4. **The bridge:** `walkTransitionMatrix M = M` entrywise — `deg M i = 1`
   by the row sums, `walkTransitionMatrix_apply` reduces to
   `1⁻¹ * M i j = M i j`.
5. **The composition:** apply the delivered
   `exists_stationaryVec_of_irreducible` /
   `existsUnique_stationaryVec_of_irreducible` /
   `stationaryVec_pos_of_irreducible` at `A := G` with the hypotheses
   from steps 1–3, then rewrite the conclusion through the bridge. The
   two axiom applications stay inside the delivered layer; this module
   adds none.

## QA obligations (all mandatory)

1. **Reducible-input positive witness** (the two disjoint `Fin 4`
   edges, `α = 1/2`, reusing `IrreducibleStationary_QA`'s `A4`
   fixture): the `∃!` instantiated; the hand value — uniform
   `(1/4,1/4,1/4,1/4)`, forced by the fixture's vertex-transitivity —
   verified **completely raw** (nonnegativity, mass, and all four
   stationarity coordinates against pinned `G` entries); the contrast
   pinned: the *raw* walk on the same fixture has two stationary
   distributions (the prior fence), the teleported walk exactly one.
2. **Asymmetric fixture with a non-uniform PageRank** (the `Fin 3`
   star, `α = 1/2`, reusing `A3` and its pinned walk entries):
   PageRank `= (4/9, 5/18, 5/18)` verified raw; provably distinct from
   the raw stationary `(1/2, 1/4, 1/4)` — teleportation shifts mass to
   the leaves, the actual content of the construction; every stationary
   distribution of `G` equals the hand value (the `∃!` join).
3. **Structural pins:** the teleportation floor at a zero-support pair
   (`0 < G 0 3` pinned to the exact `1/8`); an entry pin at a support
   pair (`G 0 1 = 5/8`); row sums raw; the bridge instantiated
   (`walkTransitionMatrix (googleMatrix A4 (1/2)) = googleMatrix A4 (1/2)`).
4. **Fences (both endpoints, complementary fixtures, hypotheses other
   than the fenced one verified intact):**
   - `α = 1` on the reducible fixture: `googleMatrix A4 1 =
     walkTransitionMatrix A4` pinned; the hypothesis-free `∃!`
     conclusion **refuted in proved form** through the prior
     `pi4a`/`pi4b` witnesses (row sums, nonnegativity, degrees all
     intact — exactly `hα2` isolated).
   - `α = -1` on `K₂`: `googleMatrix edge (-1) = 1` pinned (the
     degenerate collapse — negative teleportation weight cancels the
     walk entirely); the `∃!` refuted (`(1,0)` and `(0,1)` both
     stationary, both distributions); row stochasticity *still holds*
     (it is α-free) — exactly `hα` isolated.

## Acceptance bar

- The module compiles directly with zero errors/warnings; `#print
  axioms` on the three conditional theorems reads `perron_frobenius`
  plus the standard three — reported honestly, never described as
  foundationally proved. The structural layer (floor, irreducibility,
  row sums, bridge) reads only the standard three.
- QA has no `sorry`/`admit`; its axiom-consuming declarations list
  `perron_frobenius`, its raw ones do not.
- Zero new axioms (count stays 9); citation surface unchanged (the
  construction's provenance noted in the module docstring at
  section-level locator only, routed through the axiom's Horn–Johnson
  record for the mathematical content; no page numbers invented).
- `index/map/spectral_graph.md` gains the module's declarations;
  `docs/6_SGT_BACKLOG.md` item 8 records the second named consumer
  delivered.

## Delivery record

**DELIVERED 2026-08-24 (run `20260824T045932Z-run-1`) — Steps 0+1 in
one run, zero new axioms (count stays 9), QA 1715 → 1804
(`PageRank_QA` a new file at 89 by the generator metric, 85 counted
by declaration grep).**

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/PageRank.lean`
(namespace `SpectralGraphTheory`; minimal imports —
IrreducibleStationary + Normalized; the umbrella importing it) — the
nine unconditional structural declarations (`googleMatrix` with its
`_apply` entry form; `walkTransitionMatrix_nonneg` (the sign-pattern
reading, previously only inline in the parent engine);
`googleMatrix_nonneg` on `[0,1]`; **`googleMatrix_pos`** — the
teleportation floor, `0 < G i j` at every pair on `[0,1)` with
nonempty `V`, from the additive weight `(1−α)·(card V)⁻¹` alone;
`googleMatrix_row_sum` — α-free row stochasticity (affine; survives
both fence endpoints); `googleMatrix_deg_eq_one`; **`googleMatrix_isIrreducible`**
— one `ReflTransGen.single` per pair through the floor, no hypothesis
on the input beyond nonnegativity and positive degrees; and
**`walkTransitionMatrix_eq_of_row_sum_one`** — the general
row-stochasticity bridge, deliberately stated at any matrix so future
row-stochastic consumers compose the same way) and the three
axiom-**conditional** theorems: `exists_pageRankVec` (strictly
positive, mass-one `π ᵥ* G = π`), `existsUnique_pageRankVec` (the
`∃!` among nonnegative distributions, **no irreducibility hypothesis
on the input**), and `pageRankVec_pos` (full support). All three are
pure compositions — the parent layer's theorems applied at
`M := googleMatrix A α` with `hnn`/`hirr`/`hex`/`hdeg` all derived
structurally, the conclusion translated through the bridge; **zero
new axiom contact** (the two axiom applications stay inside the
delivered `IrreducibleStationary` engine, verified by `#print axioms`).

**QA (+89, `Scaffold/QA/SpectralGraph/PageRank_QA.lean`, reusing
`IrreducibleStationary_QA`'s fixtures by QA-to-QA import):** all four
mandated sections. (1) Structural on the reducible two-edge fixture
at `α = 1/2`: all 16 Google entries pinned (`1/8` floor, `5/8`
edges), the floor at the zero-support pair `(0,3)` by theorem *and*
raw route, row sums both routes, the bridge instantiated
(`walkTransitionMatrix A4G = A4G`), irreducibility on input whose own
irreducibility provably fails. (2) The reducible-input positive
witness: uniform `(1/4,1/4,1/4,1/4)` verified **completely raw** (all
four stationarity coordinates against the pinned entries — the column
sums meeting the row sums at the same arithmetic), the `∃!`
instantiated, and the load-bearing join `A4G_stationary_eq_uniform_QA`
identifying *every* stationary distribution with the hand value — on
the very fixture whose raw walk has two (the imported fence). (3) The
asymmetric star at `α = 1/2`: PageRank `(4/9, 5/18, 5/18)` verified
raw (all 9 entries pinned; every stationarity coordinate by hand
arithmetic `4/9·1/6 + 5/18·2/3 + 5/18·2/3 = 4/9` etc.), the `∃!` join
`A3G_eq_hand_QA`, full support instantiated on both fixtures, and
`pr3_ne_pi3_QA` — the PageRank vector provably *distinct* from the
raw stationary `(1/2,1/4,1/4)` at the hub coordinate (teleportation
shifts mass to the leaves: the quantity PageRank exists to compute).
(4) Both endpoint fences refuted in proved form, complementary:
`A4G1_not_unique_QA` at `α = 1` (teleportation removed —
`googleMatrix A4 1 = walkTransitionMatrix A4` pinned entrywise, the
`∃!` refuted through the imported `pi4a`/`pi4b` witnesses with
nonnegativity/degrees/row sums verified intact, exactly `hα2`
isolated) and `K2Gm1_not_unique_QA` at `α = -1` on `K₂`
(`googleMatrix K2 (-1) = 1` pinned — negative teleportation weight
cancels the walk entirely — both point masses stationary and distinct,
row stochasticity *still holding* by the α-free theorem, exactly
`hα` isolated).

**Verification:** spike first (`wip/pagerank_spike.lean`, three
rounds to green; then `wip/pagerank_qa_spike.lean`, two rounds — the
fixes recorded below); `lake env lean` on the module and the QA file
— zero errors, zero warnings each; explicit `lake build` targets both
✔; `#print axioms` via `wip/pagerank_axcheck.lean` on all 12 public
+ all 85 QA declarations — the split exactly as specified (the 3
conditional public theorems and the 6 axiom-route QA theorems — the
two `∃!` instantiations, the two joins, the two full-support
instantiations — list `perron_frobenius` + the standard three; the 9
structural public declarations and all 79 other QA declarations,
including both refutation fences, only the standard three); **full
`lake build` ✔ (2258 targets, +1, "Build completed successfully";
zero warnings in the changed modules — the build log's Scaffold-tree
warnings are the documented pre-existing set in untouched modules)**;
`lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1804/9/0**,
idempotent).

**Pin-technique notes (recorded for future runs):** `∑ j` over a
constant summand leaves `j`'s type a metavariable — annotate the
binder (`∑ j : V, …`); the constant sum `∑ j, n⁻¹ = n⁻¹ * n` is built
*backwards* through `Finset.mul_sum` + a `∑ j, 1 = ↑n` lemma
(`Finset.sum_const` gives ℕ-smul for which this pin has no general
cast lemma — `rw [← hone, Finset.mul_sum]; simp` assembles it); the
`∃!` destructure needs explicit grouping `⟨π, ⟨h1, h2, h3⟩, huniq⟩`
(flat patterns coalesce onto the *last* field — the `∀`, which then
fails to destructure); `rw [bridge]` vs `rw [← bridge]` directions —
`at h` from walk-form to plain-form with the forward direction, goal
conversion with the reverse when the goal is the plain form;
`Fintype.card_pos` applied inside `Nat.cast_pos.mpr` strands a
`Fintype ?m` metavariable — isolate it in a typed `have hc` first
(the numeric-default trap's instance face); `fin_cases`-produced
`Fin.mk` indices resist literal `simp only [entry_lemma]` rewrites —
use full `simp [entry lemmas]` at predicate level or literal-index
lemmmas without `fin_cases` (both recorded traps re-hit and worked
around per the IrreducibleStationary notes); `simp` closes `0 ≤ 1/4`
but not `0 ≤ 4/9` — append `norm_num` uniformly.

**Open follow-ons (not started, per the one-step discipline):**
mixing/rate statements on the directed axis (geometric convergence of
the PageRank power iteration needs strict dominance ⇒ primitivity —
the axiom deliberately claims no such clause; a primitivity-shaped
admission would be its own proposal); the personalization-vector
generalization `E = v vᵀ` (uniform teleportation only here — the
Page–Brin source convention difference recorded in the module
docstring); the symmetric-connected → irreducible bridge lemma
(already the parent proposal's recorded follow-on).
