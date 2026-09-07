# Proposal: The Band + Normalized Inert Quartet's Positive Pins

**Status:** COMPLETE. Delivered 2026-09-07 (run `20260907T153752Z-run-1`,
session `ses_f83866b92ffeZMaPKRE7jkT5Jb`); QA-only, zero axiom contact.

## The census finding this closes

`scripts/consumption_survey.py`'s census
(`wip/census_20260907_post14.txt`) leaves the inert set at 11, headed by
the two 2-clusters whose scope decisions
`heat-irreducible-pairs-pins.md` recorded when it took the Heat and
IrreducibleStationary pairs:

- the **Band pair** — `bandProjector_mulVec_eigvecOf_eq_zero_right`
  (the mode-selection interface's right-annihilation half; its left
  sibling was pinned at delivery, this never) and
  `eq_zero_of_bandProjector_mulVec_eq_self` (the Step-2 vanishing
  statement), whose recorded scope decision was "its natural QA shape
  is a hypothesis-necessity fence (an `h₁`-breaker), which belongs to a
  Band-audit delivery, not a pins batch";
- the **Normalized pair** — `walkLaplacian_mulVec_eigvecOf` and
  `walk_eigvec_expansion`, "stated at the *opaque* spectral-theorem
  basis `eigvecOf`, whose sign is not resolvable without unfolding ...
  a pin would need sign-robust quadratic sums or an
  `eigvalOf`-identification lemma" — priced as residue.

This delivery takes all four. Both recorded obstacles dissolve:

1. **The vanishing statement's degenerate-instance concern** is
   resolved by consuming the theorem as the *engine of a concrete
   refutation* rather than pinning it at a witness: the honest positive
   form of "with disjoint bands only `w = 0` satisfies both
   fixed-point hypotheses" is the **nonexistence statement** — no
   nonzero signal is fixed by both bands of the delivered two-band
   partition — whose proof is exactly the theorem.
2. **The `eigvecOf`-opacity** is resolved by two instruments that never
   unfold the basis: a QA-local **eigenvalue-witness bridge** (hand
   eigenpair → `eigvalOf` index; confirmed necessary by Mathlib's own
   source — `eigenvectorBasis`/`eigenvalues` are built from the direct
   sum of eigenspaces with an explicit upstream TODO to sort them, so
   no index or sign is syntactically resolvable), and **sign-robust
   forms** — facts homogeneous in the eigenvector, or quadratic per
   mode so the sign cancels.

## What was delivered

Twenty-four QA declarations: Band_QA's right-annihilation and
shared-mode sections (+8: the below/above-spectrum closed-form band
values, the annihilation pin/not-fixed/numeric trio, the nonexistence
pair) and its `BandFences` h₁/h₂ pair with isolations (+4);
Normalized_QA's eigenbasis-transfer pins section (+12: the generic
bridge, the `L_sym` corner/second off-diagonal entry pins, the mode-`1`
eigenspace shape, the transfer pin/shape/raw trio, the two center
action pins, the column-completeness pin, the expansion join pair).

### Band, at the delivered `diag13` fixture (spectrum `{1, 3}`)

- `band_diag13_low_excludes_high_mode` — the eigenvalue-`3` mode
  annihilated by the low band `(−1, 2]` through
  `bandProjector_mulVec_eigvecOf_eq_zero_right` (the theorem's first
  genuine consumption; the exact mirror of the consumed
  `_eq_zero_left` pin), with `band_diag13_low_not_fix_high_mode`
  (annihilation meets a nonzero vector) and
  `band_diag13_low_kill_high_mode_numeric` (the raw cross-check: the
  pinned first-axis projector kills the second-axis eigenvector) —
  two routes, one value.
- `band_diag13_partition_share_no_mode` — the shared-mode vanishing
  statement consumed as an engine:
  `eq_zero_of_bandProjector_mulVec_eq_self` turns the two fixed-point
  hypotheses into `w = 0`, refuting the existential at the delivered
  partition `(−1, 2] ⊔ (2, 4]`; the raw companion
  `..._no_mode_raw` forces both entries to zero from the pinned axis
  band values alone.
- `band_diag13_below_spectrum` / `band_diag13_above_spectrum` — the
  closed-form empty-band values (both threshold projectors zero /
  both identity) through the extreme-threshold theorems, the
  instruments the new fences instantiate.
- `bfF_shared_h1_fence` / `bfF_shared_h2_fence` (+ isolations) — the
  audit's missing two fences for the shared-mode theorem: dropping
  either fix hypothesis, the *other* band instantiated as a covering
  band (the identity) fixes `![1,0]`, so the dropped-hypothesis
  conclusion `w = 0` fails; the dropped hypotheses genuinely fail at
  the witness (the empty bands annihilate it). All closed-form, no
  opaque values. The `hab`/`hcd` clauses admit no fence — a negated
  band is minus an honest projector (`band_diag13_four_zero`), which
  fixes only `0` — classified in prose, the primitive-convergence
  audit's no-admissible-fixture pattern.

### Normalized, at the delivered P₃ fixture (degrees `(1, 2, 1)`)

- `eigvalOf_of_eigenpair` — **the eigenvalue-witness bridge**, generic
  over the matrix: from `M *ᵥ x = μ • x` with `x ≠ 0`, an index `i`
  with `eigvalOf M hM i = μ` exists. Proof:
  `dotProduct_eigvecOf_mulVec` moves the symmetric operator across
  the dot product (the mismatch factor `(μᵢ − μ)` kills every
  expansion coefficient), and `eigvecOf_expansion_apply` collapses
  `x` — the sign-free instrument the scope decision priced as an
  "`eigvalOf`-identification lemma", delivered at exactly the needed
  strength.
- `path_eigvecOf_one_shape` — the mode-`1` eigenspace at the opaque
  basis is one-dimensional along `(1, 0, −1)` (two row equations of
  `L_sym − 1`, the new corner/off-diagonal entry pins supplying the
  row values): middle entry `0`, antisymmetric ends — scale and sign
  never resolved, because no pin below consumes them.
- `path_walkLaplacian_eigvecOf_transfer_pin` /
  `..._transfer_shape` — the bridge locates the eigenvalue-`1` index
  from the hand eigenpair `path_Lsym_eigen_one_QA`, and
  `walkLaplacian_mulVec_eigvecOf` transfers that basis vector to a
  walk-Laplacian fixed point; the shape companion reads the
  conjugated vector's sign-robust entries (middle `0`, antisymmetric,
  nonzero — wrong conjugation or wrong eigenvalue breaks these).
  `path_walkLaplacian_one_mode_raw` is the hand-eigenpair numeric
  companion (raw `P = D⁻¹A` arithmetic).
- `path_walk_eigvec_expansion_center_join` /
  `..._join_raw` — **the expansion's aggregate-quadratic join**: the
  transferred expansion of the center vertex `e₁`, dotted with the
  conjugated test vector `(1/√D) • e₁`, evaluates the whole quadratic
  sum to `(√2)⁻¹ = 1/√(deg 1)` — a value carrying the graph's genuine
  irregularity (regular graphs would give `1`). Route A dots the
  theorem's identity with the test vector; route B rewrites each
  summand by the pinned diagonal actions (`√2`, `1/√2` at the center)
  and sums the squares through the column-completeness fact
  (`eigvecOf_expansion_apply` at `e₁`) — two independent engines, one
  value, the sign-resolution the scope decision priced delivered as
  "sign-robust quadratic sums".

## Consumption closure (the tool's verdict)

The census re-run (`wip/census_20260907_post15.txt`, diffed against
`post14`) shows exactly the 4 targeted theorems leaving the inert set —
1363 → 1367 value-consumed, 11 → 7 never-touched, the Band (2) and
Normalized (2) lines gone, no bonus, no collateral. The pins method's
thirteenth application.

## Traps recorded (the spike's four fix rounds)

- `Finset.sum_congr rfl (fun i _ => …)` as an `rw` argument fails
  (higher-order pattern unification) — the explicit `calc … :=
    refine Finset.sum_congr rfl fun i _ => ?_` route instead.
- `congrArg (fun s => s ⬝ᵥ u) h` leaves the application un-beta-reduced
  and `rw [hsplit]` misses — `simp only [hsplit]` beta-reduces while
  rewriting.
- `fin_cases` eta-expansion defeats `rw [pathAdj_deg_one]` in entry
  goals — the files' established defeq-tolerant-`have` cure
  (`rcases nfFin3_cases i with rfl | rfl | rfl` in Normalized_QA;
  literal-index `have`s in Band_QA).
- A theorem with implicit `{i}` called with `i` explicitly lands `i`
  in the first *explicit* slot — the elaborator's message makes this
  cheap to catch.
- One duplicate declaration (`diag13_exists_three` — already present
  in Band_QA's partition section) caught at build time and removed:
  the QA-name-collision guard's exact defect class, this time caught
  by the elaborator before the guard ran.

## Residue

- The Normalized pair's *full* value pins (evaluating the transferred
  expansion at a general `w`, or the transfer at all three modes)
  would need the complete three-eigenspace identification plus a
  pigeonhole on the index type — priced, not owed; the aggregate join
  delivers the sign-resolution content at one fixture.
- The AlonBoppana (3) and Azuma `MatrixMDS` (3) clusters and
  `l_infty_norm_nonneg` remain the census's inert tail (7).
