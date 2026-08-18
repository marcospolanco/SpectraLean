# Proposal: The Fiedler Vector and a Certified Spectral Partition

**Status:** Phase A (A1/A2) delivered 2026-08-18; Phase B open —
decision pending on running it against the currently admitted Cheeger
hard direction or deferring until that direction is proved. The
delivery record is at the end of this file. Authorizes no further Lean
changes, axiom admissions, document rewrites, or external publication.

Assistant's assessment of project direction, requested
2026-08-18 (surface-area follow-up for the formal-methods/high-assurance
audience).

Companion to [Prove λ₂'s Variational
Characterization](prove-lambda2-variational.md) — this proposal's Phase B
benefits from that one landing but does not strictly require it — and to
`docs/6_SGT_BACKLOG.md` item 4, which names this exact interface as the
application ring's first candidate: "spectral partitioning through
lambda2/Fiedler vectors (needs a Fiedler-vector interface — currently
absent)."

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean` (`eigvecOf`,
`eigvalOf`, `eigvecOf_complete`, `eigvecOf_inner` — the eigenbasis
machinery), `Scaffold/Mathlib/GraphTheory/Cheeger.lean` (admitted bounds),
`docs/6_SGT_BACKLOG.md` item 4, and `docs/7_SGT_RADAR.md` axis 4.

## Recommendation

Deliver the Fiedler-vector interface in two phases with sharply different
trust cost, and do not conflate them: **(A)** existence and definition —
provable now from existing eigenbasis machinery, no new axioms; **(B)** a
certified partition-quality guarantee — inherits whatever trust level the
Cheeger bounds currently carry (admitted, regular-graphs-only, unless
`prove-cheeger-easy-direction.md` lands first).

## Why this axis

Named directly in backlog item 4 as the application ring's first candidate
shape, explicitly gated on "items 1–3 mak[ing] the inner interfaces
credible" — largely true now that the electrical program's steps and the
kernel/component characterization have landed. This is the concrete
surface-area direction for the formal-methods/high-assurance audience: not
more foundational SGT, but the first actual *algorithm* — something a
downstream engineer calls to get a partition, not just a theorem to cite.

## Calibration

"The Fiedler vector exists" and "the partition it induces is provably
good" are different claims with very different costs, and the gap between
them is the entire point of splitting this into two phases. Phase A is
close to free — Scaffold's eigenbasis is already proved complete and
orthonormal, so defining the vector and proving it is a genuine eigenvector
at `lambda2` is largely composition of what already exists. Phase B
requires the admitted Cheeger bounds and inherits both their trust cost and
their regular-graphs-only scope restriction. Do not present Phase A's
existence result as if it already carries Phase B's quality guarantee — a
Fiedler vector that exists but partitions badly is a real possibility this
document's own phase split exists to keep visible.

## Build order

### A1. Define the Fiedler vector

```
fiedlerVector (A : WAdj) (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) : V → ℝ :=
  eigvecOf (laplacian A) (laplacian_symmetric A hA) ⟨1, by omega⟩
```

(index `1` = second-smallest in the sorted spectrum, i.e., `lambda2`'s
position.) Prove it is a genuine eigenvector at eigenvalue `lambda2 A hA
hcard`, via the existing `eigvalOf`/`eigvecOf` agreement lemmas — largely a
direct composition of what `Spectral.lean` already proves.

### A2. Define the induced partition

```
fiedlerPartition A hA hcard : Finset V :=
  (Finset.univ).filter (fun i => 0 ≤ fiedlerVector A hA hcard i)
```

The standard sign-pattern bipartition. Prove basic sanity facts —
nonempty and proper for a connected graph with `lambda2 > 0`. This
depends on the kernel characterization from `electrical-structure-crust.md`
step 2 (`laplacian_kernel_eq_span_onesVec`) to know `lambda2 > 0` is even
the right condition to check — a genuine, already-delivered load-bearing
consumer of that step, not a restatement.

### B. The quality guarantee (Cheeger-gated)

State and prove — or explicitly derive from the admitted axiom —

```
conductance (fiedlerPartition A hA hcard) ≤ [bound in terms of lambda2]
```

composing `cheegerConstant`/`conductance` (proved, `Cheeger.lean`) with
the admitted Cheeger upper bound. This step's trust level is exactly the
Cheeger axiom's trust level — no worse, no better. If
`prove-lambda2-variational.md` has landed by the time this step is
attempted: note that it does not directly weaken this step's dependency —
Phase B needs the Cheeger *bound* itself proved, not just the variational
characterization of `lambda2` — but a proved variational characterization
is a real prerequisite for eventually proving the Cheeger bound itself, the
route `prove-cheeger-easy-direction.md` already scoped.

## Deferred and removed

- **Multiway/recursive spectral partitioning** (k-way, not 2-way) — out of
  scope. `docs/7_SGT_RADAR.md` axis 4 lists "multiway expansion" as absent;
  this proposal does not claim it.
- **The irregular-graph Cheeger generalization** — this proposal consumes
  whatever Cheeger shape currently exists (regular-only); it does not
  itself extend it. See `prove-cheeger-easy-direction.md` for that
  separate effort.

## Operating instructions for an autonomous run

- **Phase A (A1, A2) is one run, hard crust, no new axioms.**
- **Phase B is a separate run and is explicitly not hard crust** — it is
  an axiom-backed derived theorem. Label it as such in the radar re-score;
  do not let axis 4's score imply more assurance than the admitted Cheeger
  bound already carries.
- QA: A1/A2 need a positive witness (a small graph with an obvious good
  cut — e.g. two near-cliques joined by one edge — where the Fiedler
  partition is computed and checked against the known good cut), per the
  repository's standing QA convention of a positive witness plus a
  hypothesis-load-bearing negative one.
- Do not re-score `docs/7_SGT_RADAR.md` axis 4 until a phase's proof lands
  and its QA passes; score Phase A and Phase B as separate milestones, not
  one combined jump, since they carry different trust levels.

## Open next step

Run A1/A2 now — they have no dependency on `prove-lambda2-variational.md`
landing first, and there is no reason to wait for it. Decide separately,
once A1/A2 exist, whether Phase B is worth running against the currently
admitted Cheeger bound or worth deferring until
`prove-cheeger-easy-direction.md` gives it a proved foundation instead.

## Delivery record (Phase A, 2026-08-18)

Delivered as `Scaffold.Mathlib.GraphTheory.Fiedler` plus
`Scaffold/QA/SpectralGraph/Fiedler_QA.lean` (57 declarations), all
proved, **no new axioms** (count stays 16). One run, per the operating
instructions; Phase B was not started.

**A1 (`fiedlerVector`):** statement-shape deviation from the build-order
sketch, recorded before stating: the sketch wrote
`eigvecOf (laplacian A) hL ⟨1, by omega⟩`, but `eigvecOf` is indexed by
`V` (the eigenbasis listing), not by sorted-spectrum positions, so the
second-smallest eigenvalue is first located in the listing
(`evals_mem_eigvalOf`) and the index fixed by classical choice
(`fiedlerIndex`, with the interface lemma `fiedlerIndex_eigvalOf`).
Delivered: the eigenvector equation `fiedlerVector_eigen`, unit norm
(`fiedlerVector_norm`), nonvanishing, the energy identity
`fiedlerVector_quadForm` (`quadForm L f = lambda2`), and orthogonality
to `onesVec` under `0 < lambda2` (`fiedlerVector_ortho_onesVec`,
`fiedlerVector_sum_eq_zero`).

**A2 (`fiedlerPartition`):** the sign half-space, with the sanity facts
at two strengths — interface form under `0 < lambda2`
(`fiedlerPartition_nonempty_of_pos`, `fiedlerPartition_ne_univ_of_pos`)
and the connectivity corollaries. The load-bearing dependency the
proposal named landed as its own theorem:
`lambda2_pos_of_connected` (connected + symmetric nonnegative weights ⇒
`0 < lambda2`) — the algebraic-connectivity certificate, consuming
`laplacian_kernel_eq_span_onesVec` (electrical step 2), PSD, and both
multiplicity pins; its contrapositive is what makes `lambda2 > 0` the
right hypothesis (disconnected ⇒ kernel ≥ 2-dimensional ⇒ `λ₂ = 0`).

**QA (per the spec's own witness requirements):** positive witness —
the `P₄` barbell (two `K₂` near-cliques joined by one bridge edge, the
proposal's example shape): `λ₂ ≤ 1` through the proved Rayleigh engine
at the cut indicator, `λ₂ ≠ 1` from the eigen equations, and the sign
pattern *derived* from the eigen equations plus the zero sum forces
`fiedlerPartition` to be exactly the known good cut `{0, 1}` or its
complement, with boundary `1`, volume `3`, and conductance `1/3` — all
computed, not assumed; plus the `K₂` witness (partition pinned to a
singleton half through antisymmetry + unit norm, boundary `1`).
Negative witness — the disconnected two-edge fixture: the support graph
is proved not connected, `λ₂ = 0` (the hypothesis fails), and
`onesVec` is a nonzero eigenvector at that same eigenvalue (satisfying
exactly the eigen-equation A1 states) whose sign filter is all of
`univ` — so the sanity conclusions cannot follow from the eigen-property
alone; the hypothesis is load-bearing.

**Radar:** subject axis 4 re-scored 3.0 → 3.5 per the proposal's own
protocol (Phase A scored as its own milestone, hard crust; Phase B will
be scored separately at its axiom-backed trust level).

**Phase B (open):** a certified conductance bound
`conductance (fiedlerPartition …) ≤ [bound in terms of lambda2]`,
composing the proved `cheeger_upper_bound` and the *admitted*
`cheeger_lower_bound`. Note for the decision: the easy direction has
since been proved (`prove-cheeger-easy-direction.md` delivered), so a
Phase B run today would rest its lower-bound half on exactly one
admitted Cheeger statement (the hard direction); the easy-direction
half would be fully proved.
