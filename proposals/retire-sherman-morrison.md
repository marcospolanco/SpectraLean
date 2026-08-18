# Proposal: Derive and Retire the Sherman–Morrison Axiom

**Status:** Delivered 2026-08-18 (see
[Delivery record](#delivery-record) below; the original proposal text
follows unedited for the record). Sequenced after (or immediately
alongside) the in-flight [Repair and
Retire the Woodbury Identity Axiom](repair-and-retire-woodbury.md), whose
corrected theorem this proposal specializes to the rank-one case rather
than re-deriving from scratch. This document authorizes no Lean changes,
axiom removals, commits, or external publication on its own.

Companion to `repair-and-retire-woodbury.md` — this is its natural
sequel, not an independent axiom-hunting expedition. `sherman_morrison`
is literally the `k = 1` special case of the Woodbury identity, so once
the general theorem is corrected and proved, this is a short derivation
reusing the same Mathlib imports and bridge lemmas, not new proof work
from first principles.

Assessed from `Scaffold/Mathlib/Core/MatrixUpdates.lean` (both axioms),
the pinned Mathlib's `Matrix.invOf_add_mul_mul` / `invertibleAddMulMul` /
`invOf_eq_nonsing_inv` (`Data/Matrix/Invertible.lean`,
`LinearAlgebra/Matrix/NonsingularInverse.lean`), and a fresh search of
the pinned Mathlib confirming no directly-named Sherman–Morrison lemma
exists (the only "sherman" hits — `Data/Matrix/Rank.lean`,
`LinearAlgebra/FiniteDimensional.lean`,
`LinearAlgebra/Dimension/FreeAndStrongRankCondition.lean` — are
unrelated).

## Unlike Woodbury, this axiom is already stated correctly

Worth checking explicitly before treating this as a second repair job:
substituting `C = [1]` (the `1×1` identity), `U = u` (as an `n×1`
column), `V = vᵀ` (as a `1×n` row) into the **corrected** Woodbury
identity — `(A+UCV)⁻¹ = A⁻¹ − A⁻¹U(C⁻¹+VA⁻¹U)⁻¹VA⁻¹` — gives exactly
Scaffold's current `sherman_morrison` statement: `C⁻¹ = [1]` again at
rank one, so the middle term is the scalar `(1 + vᵀA⁻¹u)⁻¹`, matching the
axiom's `(1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹` factor exactly. The `C` vs. `C⁻¹` bug
that made `woodbury_identity` false doesn't produce a visible difference
at rank one, since `[1]⁻¹ = [1]`. **This is a pure proof task, not a
correctness repair** — say so explicitly in the delivery record so it
isn't read as a second instance of the Woodbury bug.

## Why this is low-hanging, and why it isn't High

- Zero current Lean consumers, confirmed by search — the same situation
  Woodbury was in before its priority was reconsidered. But there is no
  matching correctness-hazard argument here to justify overriding the
  leverage test the way Woodbury's false statement did, since this
  statement is already right. That is why this proposal is scoped as
  Medium, not High: real, cheap, unblocked work, not an urgent repair.
- No dedicated Mathlib lemma exists under this name, but the theorem is a
  direct instance of machinery `repair-and-retire-woodbury.md` is already
  wiring up. If that proposal's repair lands first, this becomes a short
  specialization, not independent proof work — the cheapest axiom
  retirement currently available in the backlog.

## Calibration — the real plumbing, not a one-line corollary

Do not treat "the `k=1` special case" as free. Scaffold's axiom is stated
in vector/entrywise form (`u v : n → 𝕜`, the outer product as
`Matrix.of (fun i j => u i * v j)`), while Mathlib's theorem is stated in
`n × k` matrix form. Bridging needs:

- packing `u` into a column matrix `U : Matrix n (Fin 1) 𝕜` and `v` into
  a row matrix `V : Matrix (Fin 1) n 𝕜`;
- proving `Matrix.of (fun i j => u i * v j) = U * V` entrywise — short
  but real, since `Matrix.mul` unfolds to a `Fin 1`-indexed sum with one
  term, not a definitional identity;
- converting the `1×1` matrix `C⁻¹ + V A⁻¹ U` into the scalar
  `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)`, which needs a `1×1`-matrix-as-scalar lemma (its
  determinant, its inverse) rather than a `rfl`.

None of this is hard, but none of it is free either; expect a small,
genuine proof, not a pure specialization by substitution.

## Scope

1. Record (as above) that no correctness repair is needed here — this
   step is proof-only, unlike Woodbury's statement-shape fix.
2. Once `repair-and-retire-woodbury.md`'s corrected theorem exists,
   specialize it at `k = Fin 1` (or `PUnit`, whichever bridges more
   cleanly to the existing `n → 𝕜` outer-product convention), producing
   the matrix-shape lemma.
3. Bridge the matrix-shape lemma to Scaffold's existing vector/entrywise
   statement via the three plumbing steps above.
4. Replace the axiom with the resulting theorem, **at its current name
   and hypotheses** (`hA : IsUnit A.det`,
   `hv : v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ -1`) — no API migration needed, unlike
   Woodbury's necessary `C → C⁻¹` public-signature change.
5. QA: one positive instance (small nonzero vectors, value checked
   independently) and a negative witness on the excluded denominator case
   (`v ⬝ᵥ (A⁻¹ *ᵥ u) = -1`), matching the standing convention.
6. Update the scoreboard, source index, and the explicit axiom count.

## Sequencing

Run this **after** (or, if convenient, immediately following in the same
session) `repair-and-retire-woodbury.md` — not before, since bridging
against the axiom's currently-buggy middle factor would need repeating
once Woodbury's corrected shape lands. If Woodbury stalls for several
sessions, this proposal could in principle proceed independently by
deriving Sherman–Morrison directly from Mathlib's `invOf_add_mul_mul`
without going through Scaffold's own Woodbury theorem at all — record
explicitly which route was actually taken, since it changes what this
proposal's delivery depends on.

## Acceptance criteria

- No `axiom`, `sorry`, or `admit` introduced.
- The corrected theorem's module and QA elaborate directly; standard
  hygiene checks and `lake build` pass.
- Axiom count decreases by one from whatever
  `repair-and-retire-woodbury.md` leaves it at.
- The delivery record states plainly that this was a proof task, not a
  correctness repair, per the finding above.

## Delivery record (2026-08-18)

Delivered in one run as scoped (items 1–6). Explicit axiom count
15 → 14.

- **Statement, plainly:** this was a **proof task, not a correctness
  repair**, per this proposal's own pre-check — the axiom's statement
  was verified against the corrected Woodbury shape before any edit,
  and at `C = [1]` the rank-one middle factor is exactly the scalar
  denominator `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)`, so the retired axiom already
  stated the correct specialization. The theorem keeps the axiom's
  exact name, hypotheses (`hA : IsUnit A.det`,
  `hv : v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ -1`), and statement; zero consumers existed,
  so there was no migration surface.
- **Route (as proposed, through Scaffold's own Woodbury theorem, not a
  direct `invOf_add_mul_mul` derivation):** `woodbury_identity` applied
  at `k = Fin 1` with `C = 1`; the packing lemma
  `U * V = Matrix.of fun i j => u i * v j` (`Fin.sum_univ_one`, not
  `rfl`); the middle factor identified with the 1×1 matrix of the
  scalar denominator (through `Matrix.dotProduct_mulVec`, as
  calibrated); `hM` from `hv` via `Matrix.det_fin_one`; the middle
  inverse via `Matrix.inv_eq_left_inv` with `inv_mul_cancel₀`; the
  final entrywise↔matrix shape matched by the pin's `Matrix.mul_smul` /
  `Matrix.smul_mul` algebra. `Matrix.inv_one` does not exist in the
  pin; `(1)⁻¹ = 1` was derived through `inv_eq_left_inv`.
- **Load-bearing:** the specialization consumes the repaired Woodbury
  theorem, so a residual defect in that repair would surface here
  rather than pass beside it.
- **QA (`Scaffold/QA/Core/MatrixUpdates_QA.lean`, +4 declarations):**
  positive instance at the existing `A2 = diag 2 2` fixture with
  `u = v = ![1,1]` — the update `!![3,1;1,3]`'s true inverse
  `!![3/8,-1/8;-1/8,3/8]` computed independently by the adjugate
  formula (`sherman_morrison_sum_inv_QA`), and the theorem-consumed
  right side pinned to the same value with the scalar denominator
  computed to `1` from the definitions (`sherman_morrison_rhs_QA`);
  negative witness at the excluded denominator — `A = !![1]`,
  `u = ![2]`, `v = ![-1/2]` attains `v ⬝ᵥ (A⁻¹ *ᵥ u) = -1` exactly
  (`sherman_morrison_excluded_denominator_QA`) and the update is the
  singular zero matrix there (`sherman_morrison_singular_witness_QA`),
  the point where no inverse identity could hold.
- **Records:** module docstring and theorem documentation, both
  indexes (`index/sources/higham_matrix_updates.md`,
  `index/map/perturbation.md`), scoreboard (14/480/0, milestone bullet,
  verification rows), radar (axiom-minimization trend extended to
  26 → … → 14, QA-axis count synced 480/27), README (14 axioms, 480
  QA), `proposals/README.md` (moved to Delivered).
- **Verification:** `lake env lean` on `Core.MatrixUpdates` and
  `QA.Core.MatrixUpdates_QA` — both zero errors, zero warnings;
  `lake build` of both targets ✔; full `lake build` ✔ (2179 targets);
  `lint_axioms`, `check_citations` pass; `check_markdown_links` reports
  only the operator's untracked `cdx-clean-assess.md` links (pre-existing
  at run start, outside this milestone); scoreboard regenerated and
  re-checked after the manual prose edits.
