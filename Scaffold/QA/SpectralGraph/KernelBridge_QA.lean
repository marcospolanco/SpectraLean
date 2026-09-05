/-
  KernelBridge_QA.lean

  Purpose
  -------
  QA for the kernel-equality bridge of proposal
  `proposals/electrical-structure-crust.md` step 3, delivered in
  `Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter`
  (`ker_laplacian_eq_ker_supportGraph_lapMatrix`,
  `finrank_ker_laplacian_eq_card_supportGraph_components`,
  `laplacian_ker_basis`, `laplacian_ker_basis_apply`) and its weighted
  center dependency `laplacian_mulVec_eq_zero_iff_forall_reachable`
  (`Spectral.lean`).

  Fixtures are those of `Connectivity_QA` (imported for reuse): a
  connected positive witness (the three-vertex path, where the bridge
  must agree with the connected span characterization — dimension one,
  single basis vector constantly `1`) and a disconnected negative
  witness (two disjoint edges on `Fin 4`, where the component count is
  computed to `2` independently of the transferred theorem and the
  basis vectors are computed to the component indicators
  `![1,1,0,0]`/`![0,0,1,1]` — a kernel strictly larger than the
  constants, showing the disconnected hypothesis regime is real and
  the connectivity hypothesis of the span form is load-bearing).

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is fully evaluated.

  The `BridgeFences` section below (proposal
  `proposals/adversarial-fences-kernel-bridge-family.md`, 2026-09-04)
  adds the adversarial-review fence audit: hypothesis-form negative
  witnesses for every fenceable `hnonneg` clause of the bridge and its
  weighted center dependency chain (plus the pos-weight engine's
  proof-internal `hA`), at three new signed/asymmetric fixtures —
  none of which the nonnegative fixtures above could serve.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter
import Scaffold.QA.SpectralGraph.Connectivity_QA

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## Connected witness: the three-vertex path `0 — 1 — 2`

The bridge must agree with the connected span characterization
(`Connectivity_QA.connPath_span_QA`): kernel = line of constants,
dimension one, and the single basis vector is constantly `1`.
-/

/-- Bridge instantiation on the connected path: the weighted kernel is
the Mathlib `lapMatrix` kernel of the support graph. -/
theorem connPath_bridge_QA :
    LinearMap.ker (Matrix.mulVecLin (laplacian connPathAdj))
      = LinearMap.ker (Matrix.toLin'
          ((supportGraph connPathAdj connPathAdj_isSymm).lapMatrix ℝ)) :=
  ker_laplacian_eq_ker_supportGraph_lapMatrix connPathAdj connPathAdj_isSymm
    connPathAdj_nonneg

/-- The support graph of the path has exactly one component — computed
from connectivity (a preconnected graph has subsingleton component
quotient), not from the kernel. -/
theorem connPath_card_components_eq_one_QA :
    Fintype.card (supportGraph connPathAdj connPathAdj_isSymm).ConnectedComponent
      = 1 := by
  have hsub : Subsingleton
      (supportGraph connPathAdj connPathAdj_isSymm).ConnectedComponent :=
    connPath_supportGraph_connected.preconnected.subsingleton_connectedComponent
  exact Fintype.card_eq_one_iff.mpr
    ⟨SimpleGraph.connectedComponentMk
      (supportGraph connPathAdj connPathAdj_isSymm) 0,
      fun y => hsub.elim y _⟩

/-- Dimension one: the transferred count instantiates on the path. -/
theorem connPath_finrank_eq_one_QA :
    Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (laplacian connPathAdj)))
      = 1 := by
  rw [finrank_ker_laplacian_eq_card_supportGraph_components connPathAdj
    connPathAdj_isSymm connPathAdj_nonneg, connPath_card_components_eq_one_QA]

/-- Cross-coherence, negative-witness style: the bridge's dimension
count and the connected span characterization
(`laplacian_kernel_eq_span_onesVec`, step 1 of the proposal) must hold
*simultaneously* — a mis-stated bridge (e.g. trivial kernel) would
give dimension `0`, contradicting the span form. -/
theorem connPath_bridge_coherent_QA :
    LinearMap.ker (Matrix.mulVecLin (laplacian connPathAdj))
      = Submodule.span ℝ ({onesVec} : Set (Fin 3 → ℝ))
      ∧ Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (laplacian connPathAdj))) = 1 :=
  ⟨connPath_span_QA, connPath_finrank_eq_one_QA⟩

open Classical in
/-- The single basis vector of the connected fixture is the constant-one
function — computed entrywise from the indicator interface, not from a
general theorem. -/
theorem connPath_basis_indicator_eq_one_QA (j : Fin 3) :
    ((laplacian_ker_basis connPathAdj connPathAdj_isSymm connPathAdj_nonneg
      (SimpleGraph.connectedComponentMk
        (supportGraph connPathAdj connPathAdj_isSymm) 0) : Fin 3 → ℝ) j) = 1 := by
  rw [laplacian_ker_basis_apply, if_pos
    (SimpleGraph.ConnectedComponent.sound
      (connPath_supportGraph_connected j 0))]

/-!
## Disconnected witness: two disjoint edges `0 — 1   2 — 3` on `Fin 4`

The component count is computed to `2` from the block structure of the
fixture (independent of the transferred theorem); the transferred
dimension statement then reads `finrank = 2`; the basis vectors are
computed to the component indicators; and the kernel is strictly
larger than the constants.
-/

/-- The two block representatives are distinct components: equality
would give a support-graph walk from `0` to `2`, which cannot leave
its block. -/
theorem connDisc_mk0_ne_mk2 :
    (supportGraph connDiscAdj connDiscAdj_isSymm).connectedComponentMk 0
      ≠ (supportGraph connDiscAdj connDiscAdj_isSymm).connectedComponentMk 2 := by
  intro h
  obtain ⟨w⟩ := SimpleGraph.ConnectedComponent.exact h
  have hb := connDisc_walk_blocks w
  rw [show (0 : Fin 4).val = 0 from rfl, show (2 : Fin 4).val = 2 from rfl] at hb
  omega

/-- Component equalities along the two edges. -/
theorem connDisc_mk1_eq_mk0 :
    (supportGraph connDiscAdj connDiscAdj_isSymm).connectedComponentMk 1
      = (supportGraph connDiscAdj connDiscAdj_isSymm).connectedComponentMk 0 :=
  SimpleGraph.ConnectedComponent.sound
    ((supportGraph_adj.2 ⟨by decide, by simp [connDiscAdj]⟩).reachable)

theorem connDisc_mk3_eq_mk2 :
    (supportGraph connDiscAdj connDiscAdj_isSymm).connectedComponentMk 3
      = (supportGraph connDiscAdj connDiscAdj_isSymm).connectedComponentMk 2 :=
  SimpleGraph.ConnectedComponent.sound
    ((supportGraph_adj.2 ⟨by decide, by simp [connDiscAdj]⟩).reachable)

/-- Every component is one of the two block representatives — computed
by case analysis over the four vertices. -/
theorem connDisc_component_classification (c :
    (supportGraph connDiscAdj connDiscAdj_isSymm).ConnectedComponent) :
    c = (supportGraph connDiscAdj connDiscAdj_isSymm).connectedComponentMk 0
      ∨ c = (supportGraph connDiscAdj connDiscAdj_isSymm).connectedComponentMk 2 := by
  obtain ⟨v, hv⟩ := Quot.exists_rep c
  subst hv
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inl connDisc_mk1_eq_mk0
  · exact Or.inr rfl
  · exact Or.inr connDisc_mk3_eq_mk2

/-- **Component count computed independently:** the fixture has exactly
two connected components — from the classification above plus the
distinctness of the two representatives, via `Nat.card_eq_two_iff`;
no kernel theorem is used. -/
theorem connDisc_card_components_eq_two_QA :
    Fintype.card
      ((supportGraph connDiscAdj connDiscAdj_isSymm).ConnectedComponent) = 2 := by
  classical
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff]
  refine
    ⟨SimpleGraph.connectedComponentMk (supportGraph connDiscAdj connDiscAdj_isSymm) 0,
      SimpleGraph.connectedComponentMk (supportGraph connDiscAdj connDiscAdj_isSymm) 2,
      connDisc_mk0_ne_mk2, ?_⟩
  rw [Set.eq_univ_iff_forall]
  intro c
  rcases connDisc_component_classification c with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Dimension two: the transferred component-count statement reads
`finrank = 2` on the fixture. -/
theorem connDisc_finrank_eq_two_QA :
    Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (laplacian connDiscAdj)))
      = 2 := by
  rw [finrank_ker_laplacian_eq_card_supportGraph_components connDiscAdj
    connDiscAdj_isSymm connDiscAdj_nonneg, connDisc_card_components_eq_two_QA]

open Classical in
/-- Basis vector of the first component, computed entrywise from the
indicator interface: `![1, 1, 0, 0]`. -/
theorem connDisc_basis_mk0_indicator_QA :
    (fun j => ((laplacian_ker_basis connDiscAdj connDiscAdj_isSymm
      connDiscAdj_nonneg (SimpleGraph.connectedComponentMk
        (supportGraph connDiscAdj connDiscAdj_isSymm) 0) : Fin 4 → ℝ) j))
      = ![1, 1, 0, 0] := by
  funext j
  rw [laplacian_ker_basis_apply]
  fin_cases j
  · split_ifs with h
    · simp
    · exact absurd rfl h
  · split_ifs with h
    · simp
    · exact absurd connDisc_mk1_eq_mk0 h
  · split_ifs with h
    · exact absurd h.symm connDisc_mk0_ne_mk2
    · simp
  · split_ifs with h
    · exact absurd (h.symm.trans connDisc_mk3_eq_mk2) connDisc_mk0_ne_mk2
    · simp

open Classical in
/-- Basis vector of the second component, computed entrywise from the
indicator interface: `![0, 0, 1, 1]`. -/
theorem connDisc_basis_mk2_indicator_QA :
    (fun j => ((laplacian_ker_basis connDiscAdj connDiscAdj_isSymm
      connDiscAdj_nonneg (SimpleGraph.connectedComponentMk
        (supportGraph connDiscAdj connDiscAdj_isSymm) 2) : Fin 4 → ℝ) j))
      = ![0, 0, 1, 1] := by
  funext j
  rw [laplacian_ker_basis_apply]
  fin_cases j
  · split_ifs with h
    · exact absurd h connDisc_mk0_ne_mk2
    · simp
  · split_ifs with h
    · exact absurd (connDisc_mk1_eq_mk0.symm.trans h) connDisc_mk0_ne_mk2
    · simp
  · split_ifs with h
    · simp
    · exact absurd rfl h
  · split_ifs with h
    · simp
    · exact absurd connDisc_mk3_eq_mk2 h

/-- **The connectivity hypothesis of the span form is load-bearing:** on
the disconnected fixture the weighted kernel is strictly larger than
the constant line — the component indicator `![1,1,0,0]` is a
non-constant kernel vector (computed in `Connectivity_QA`), and the
kernel dimension is `2` (computed above) — while the two basis vectors
are exactly the two component indicators. -/
theorem connDisc_kernel_exceeds_constants_QA :
    (laplacian connDiscAdj).mulVec ![1, 1, 0, 0] = 0
      ∧ (¬∃ c : ℝ, (![1, 1, 0, 0] : Fin 4 → ℝ) = fun _ => c)
      ∧ Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (laplacian connDiscAdj))) = 2 :=
  ⟨connDisc_indicator_in_kernel_QA, connDisc_indicator_not_const_QA,
    connDisc_finrank_eq_two_QA⟩

/-!
## BridgeFences: the adversarial fence audit (proposal `adversarial-fences-kernel-bridge-family.md`)

Hypothesis-form negative witnesses for the kernel-bridge family
(`SimpleGraphAdapter.lean`'s kernel-equality bridge plus the weighted
center characterization chain), whose QA (2026-08-18-era) predates the
adversarial-review discipline and instantiated only nonnegative
fixtures. Three new fixtures:

- `kbfNegEdge2Adj` (Fin 2): symmetric, one negative edge, edgeless
  support — kills the `hnonneg` clauses whose dropped statements'
  support-graph side goes junk (`RHS` trivially true / `lapMatrix = 0`
  / two components).
- `kbfSgnPath3Adj` (Fin 3): symmetric, signed, *connected* support
  (the path `0—1—2`; the negative edge `(0,2)` is not a support edge)
  — kills the `hnonneg` clauses that need genuine connectivity, with
  the kernel vector `![1,2,3]`.
- `kbfAsymSinkAdj` (Fin 3): asymmetric, *nonnegative* (only `hA`
  fails) — kills the pos-weight engine's `hA`, the family's only
  `supportGraph`-free statement.
-/

section BridgeFences

/-! ### Fixture α: the negative edge `!![0, -1; -1, 0]]` on `Fin 2` -/

/-- The negative-edge fixture: symmetric, one negative edge, no
positive entry — the support graph is edgeless (two components). -/
def kbfNegEdge2Adj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, -1; -1, 0]

theorem kbfNegEdge2Adj_isSymm : kbfNegEdge2Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem kbfNegEdge2_00 : kbfNegEdge2Adj 0 0 = 0 := rfl
theorem kbfNegEdge2_01 : kbfNegEdge2Adj 0 1 = -1 := rfl
theorem kbfNegEdge2_10 : kbfNegEdge2Adj 1 0 = -1 := rfl
theorem kbfNegEdge2_11 : kbfNegEdge2Adj 1 1 = 0 := rfl

/-- **Isolation:** the fixture genuinely violates `hnonneg`. -/
theorem kbfNegEdge2_not_nonneg : ¬ ∀ i j : Fin 2, 0 ≤ kbfNegEdge2Adj i j := by
  intro h
  have h01 := h 0 1
  rw [kbfNegEdge2_01] at h01
  norm_num at h01

/-- Entry disjunction (the entry-table route: `-1` entries defeat
simp's numeral unification, so cases go through `rfl`-lemmas). -/
theorem kbfNegEdge2_entry (i j : Fin 2) :
    kbfNegEdge2Adj i j = 0 ∨ kbfNegEdge2Adj i j = -1 := by
  fin_cases i <;> fin_cases j <;>
    first | exact Or.inl rfl | exact Or.inr rfl

/-- No support-graph adjacency anywhere. -/
theorem kbfNegEdge2_noAdj : ∀ i j : Fin 2,
    ¬ (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).Adj i j := by
  intro i j
  rw [supportGraph_adj]
  rintro ⟨-, hpos⟩
  rcases kbfNegEdge2_entry i j with h | h <;> rw [h] at hpos <;> norm_num at hpos

/-- Support-graph reachability is equality on the edgeless support. -/
theorem kbfNegEdge2_walk_eq (i j : Fin 2)
    (w : (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).Walk i j) : i = j := by
  induction w with
  | nil => rfl
  | cons hadj _ _ => exact absurd hadj (kbfNegEdge2_noAdj _ _)

theorem kbfNegEdge2_reachable_iff_eq (i j : Fin 2) :
    (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).Reachable i j ↔ i = j := by
  constructor
  · rintro ⟨w⟩
    exact kbfNegEdge2_walk_eq i j w
  · rintro rfl
    exact ⟨SimpleGraph.Walk.nil⟩

/-- **Component count, computed independently:** the edgeless support
has exactly two components. -/
theorem kbfNegEdge2_card_components_eq_two :
    Fintype.card
      (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).ConnectedComponent = 2 := by
  have hmk : (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).connectedComponentMk 0
      ≠ (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).connectedComponentMk 1 := by
    intro h
    obtain ⟨w⟩ := SimpleGraph.ConnectedComponent.exact h
    have := kbfNegEdge2_walk_eq 0 1 w
    exact absurd this (by decide)
  classical
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff]
  refine
    ⟨SimpleGraph.connectedComponentMk (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm) 0,
      SimpleGraph.connectedComponentMk (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm) 1,
      hmk, ?_⟩
  rw [Set.eq_univ_iff_forall]
  intro c
  obtain ⟨v, rfl⟩ := Quot.exists_rep c
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Row equations of the fixture Laplacian: `(L *ᵥ f) i = f (1-i) - f i`. -/
theorem kbfNegEdge2_mulVec_row0 (f : Fin 2 → ℝ) :
    ((laplacian kbfNegEdge2Adj).mulVec f) 0 = f 1 - f 0 := by
  rw [laplacian_mulVec_apply, Fin.sum_univ_two, kbfNegEdge2_00, kbfNegEdge2_01]
  ring

theorem kbfNegEdge2_mulVec_row1 (f : Fin 2 → ℝ) :
    ((laplacian kbfNegEdge2Adj).mulVec f) 1 = f 0 - f 1 := by
  rw [laplacian_mulVec_apply, Fin.sum_univ_two, kbfNegEdge2_10, kbfNegEdge2_11]
  ring

theorem kbfNegEdge2_eq_smul (f : Fin 2 → ℝ) (h : f 1 - f 0 = 0) :
    f = (f 1) • (![1, 1] : Fin 2 → ℝ) := by
  funext i
  fin_cases i
  · show f 0 = f 1 * 1
    linarith
  · show f 1 = f 1 * 1
    ring

/-- The kernel of the fixture Laplacian is exactly the constant line. -/
theorem kbfNegEdge2_kernel_eq_span :
    LinearMap.ker (Matrix.mulVecLin (laplacian kbfNegEdge2Adj))
      = Submodule.span ℝ ({![1, 1]} : Set (Fin 2 → ℝ)) := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hf
    have h0 : f 1 - f 0 = 0 := by
      have := congrFun hf 0
      rwa [kbfNegEdge2_mulVec_row0] at this
    rw [Submodule.mem_span_singleton]
    exact ⟨f 1, (kbfNegEdge2_eq_smul f h0).symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    fin_cases i
    · show ((laplacian kbfNegEdge2Adj).mulVec (![1, 1] : Fin 2 → ℝ)) 0 = (0 : Fin 2 → ℝ) 0
      rw [kbfNegEdge2_mulVec_row0]
      norm_num
    · show ((laplacian kbfNegEdge2Adj).mulVec (![1, 1] : Fin 2 → ℝ)) 1 = (0 : Fin 2 → ℝ) 1
      rw [kbfNegEdge2_mulVec_row1]
      norm_num

theorem kbfNegEdge2_finrank_ker :
    Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (laplacian kbfNegEdge2Adj))) = 1 := by
  rw [kbfNegEdge2_kernel_eq_span]
  exact finrank_span_singleton (by
    intro h
    have := congrFun h 0
    simp at this)

theorem kbfNegEdge2_mulVec_e0_ne_zero :
    (laplacian kbfNegEdge2Adj).mulVec (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [kbfNegEdge2_mulVec_row0, Matrix.cons_val_one, Matrix.head_cons] at h0
  norm_num at h0

/-- **Fence (iff, ← direction):** the dropped-`hnonneg`
`laplacian_mulVec_eq_zero_iff_forall_reachable` is false here — the
RHS is junk-trivially true (edgeless support: reachability is
equality) while `L *ᵥ ![1, 0] = ![-1, 1] ≠ 0`. -/
theorem kbfNegEdge2_iff_left_fence_QA :
    ¬ ((laplacian kbfNegEdge2Adj).mulVec (![1, 0] : Fin 2 → ℝ) = 0 ↔
        ∀ i j : Fin 2,
          (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).Reachable i j →
            (![1, 0] : Fin 2 → ℝ) i = (![1, 0] : Fin 2 → ℝ) j) := by
  intro h
  have hR : ∀ i j : Fin 2,
      (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).Reachable i j →
        (![1, 0] : Fin 2 → ℝ) i = (![1, 0] : Fin 2 → ℝ) j := by
    intro i j hr
    rw [(kbfNegEdge2_reachable_iff_eq i j).1 hr]
  exact absurd (h.mpr hR) kbfNegEdge2_mulVec_e0_ne_zero

/-- **Fence (← half):** the dropped-`hnonneg`
`laplacian_mulVec_eq_zero_of_forall_reachable` fails at the same
witness: the hypothesis is junk-satisfiable while the conclusion is
false. -/
theorem kbfNegEdge2_of_forall_fence_QA :
    ¬ ((∀ i j : Fin 2,
          (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).Reachable i j →
            (![1, 0] : Fin 2 → ℝ) i = (![1, 0] : Fin 2 → ℝ) j) →
        (laplacian kbfNegEdge2Adj).mulVec (![1, 0] : Fin 2 → ℝ) = 0) := by
  intro h
  have hR : ∀ i j : Fin 2,
      (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).Reachable i j →
        (![1, 0] : Fin 2 → ℝ) i = (![1, 0] : Fin 2 → ℝ) j := by
    intro i j hr
    rw [(kbfNegEdge2_reachable_iff_eq i j).1 hr]
  exact absurd (h hR) kbfNegEdge2_mulVec_e0_ne_zero

/-- **Fence (bridge, edgeless orientation):** the dropped-`hnonneg`
kernel-equality bridge is false — `![1, 0]` lies in the support
graph's `lapMatrix` kernel (edgeless: `lapMatrix = 0`) but not in the
weighted Laplacian's kernel. -/
theorem kbfNegEdge2_bridge_fence_QA :
    ¬ (LinearMap.ker (Matrix.mulVecLin (laplacian kbfNegEdge2Adj))
        = LinearMap.ker (Matrix.toLin'
            ((supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).lapMatrix ℝ))) := by
  intro h
  have himpl : ∀ g : Fin 2 → ℝ,
      Matrix.toLin'
          ((supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).lapMatrix ℝ) g = 0 ↔
        ∀ i j : Fin 2,
          (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).Reachable i j → g i = g j :=
    (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable
  have hmem : Matrix.toLin'
      ((supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).lapMatrix ℝ)
      (![1, 0] : Fin 2 → ℝ) = 0 := by
    rw [himpl]
    intro i j hr
    rw [(kbfNegEdge2_reachable_iff_eq i j).1 hr]
  have hmem' : (![1, 0] : Fin 2 → ℝ)
      ∈ LinearMap.ker (Matrix.toLin'
          ((supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).lapMatrix ℝ)) := by
    rw [LinearMap.mem_ker]
    exact hmem
  rw [← h] at hmem'
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem'
  exact kbfNegEdge2_mulVec_e0_ne_zero hmem'

/-- **Fence (component count):** the dropped-`hnonneg` dimension
statement is false — the weighted kernel has dimension `1` (the
constant line) against `2` components of the edgeless support. -/
theorem kbfNegEdge2_finrank_fence_QA :
    ¬ (Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (laplacian kbfNegEdge2Adj)))
        = Fintype.card
            (supportGraph kbfNegEdge2Adj kbfNegEdge2Adj_isSymm).ConnectedComponent) := by
  intro h
  rw [kbfNegEdge2_finrank_ker, kbfNegEdge2_card_components_eq_two] at h
  norm_num at h

/-! ### Fixture β: the signed path `!![0, 2, -1; 2, 0, 2; -1, 2, 0]]` on `Fin 3` -/

/-- The signed-path fixture: symmetric, signed, support the connected
path `0—1—2` (the negative edge `(0,2)` is dropped by the support
construction). -/
def kbfSgnPath3Adj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 2, -1; 2, 0, 2; -1, 2, 0]

theorem kbfSgnPath3Adj_isSymm : kbfSgnPath3Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem kbfSgn3_00 : kbfSgnPath3Adj 0 0 = 0 := rfl
theorem kbfSgn3_01 : kbfSgnPath3Adj 0 1 = 2 := rfl
theorem kbfSgn3_02 : kbfSgnPath3Adj 0 2 = -1 := rfl
theorem kbfSgn3_10 : kbfSgnPath3Adj 1 0 = 2 := rfl
theorem kbfSgn3_11 : kbfSgnPath3Adj 1 1 = 0 := rfl
theorem kbfSgn3_12 : kbfSgnPath3Adj 1 2 = 2 := rfl
theorem kbfSgn3_20 : kbfSgnPath3Adj 2 0 = -1 := rfl
theorem kbfSgn3_21 : kbfSgnPath3Adj 2 1 = 2 := rfl
theorem kbfSgn3_22 : kbfSgnPath3Adj 2 2 = 0 := rfl

/-- **Isolation:** the fixture genuinely violates `hnonneg`. -/
theorem kbfSgn3_not_nonneg : ¬ ∀ i j : Fin 3, 0 ≤ kbfSgnPath3Adj i j := by
  intro h
  have h02 := h 0 2
  rw [kbfSgn3_02] at h02
  norm_num at h02

/-- The support walks (data, not propositions, so the witnesses are
`def`s): the fence orientation `0 → 1` and the center-anchored pair
`1 → 0`, `1 → 2` used for connectivity. -/
def kbfSgn3_walk01 :
    (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Walk 0 1 :=
  SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
    ⟨by decide, by rw [kbfSgn3_01]; norm_num⟩ SimpleGraph.Walk.nil

def kbfSgn3_walk10 :
    (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Walk 1 0 :=
  SimpleGraph.Walk.cons (u := 1) (v := 0) (w := 0)
    ⟨by decide, by rw [kbfSgn3_10]; norm_num⟩ SimpleGraph.Walk.nil

def kbfSgn3_walk12 :
    (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Walk 1 2 :=
  SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
    ⟨by decide, by rw [kbfSgn3_12]; norm_num⟩ SimpleGraph.Walk.nil

/-- **Isolation (the co-hypothesis discipline):** the fixture's support
graph is genuinely *connected* — required, because `hconn` is a
co-hypothesis of the span and exists-const forms being fenced. -/
theorem kbfSgnPath3_supportGraph_connected :
    (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Connected := by
  have hfrom1 : ∀ v : Fin 3,
      (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Reachable 1 v := by
    intro v
    fin_cases v
    · exact ⟨kbfSgn3_walk10⟩
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨kbfSgn3_walk12⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨1, hfrom1⟩

theorem kbfSgnPath3_card_components_eq_one :
    Fintype.card
      (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).ConnectedComponent = 1 := by
  have hsub : Subsingleton
      (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).ConnectedComponent :=
    kbfSgnPath3_supportGraph_connected.preconnected.subsingleton_connectedComponent
  exact Fintype.card_eq_one_iff.mpr
    ⟨SimpleGraph.connectedComponentMk
      (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm) 0,
      fun y => hsub.elim y _⟩

theorem kbfSgn3_kernel_vec :
    (laplacian kbfSgnPath3Adj).mulVec (![1, 2, 3] : Fin 3 → ℝ) = 0 := by
  funext i
  fin_cases i
  · show ((laplacian kbfSgnPath3Adj).mulVec (![1, 2, 3] : Fin 3 → ℝ)) 0
        = (0 : Fin 3 → ℝ) 0
    rw [laplacian_mulVec_apply, Fin.sum_univ_three, kbfSgn3_00, kbfSgn3_01, kbfSgn3_02]
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  · show ((laplacian kbfSgnPath3Adj).mulVec (![1, 2, 3] : Fin 3 → ℝ)) 1
        = (0 : Fin 3 → ℝ) 1
    rw [laplacian_mulVec_apply, Fin.sum_univ_three, kbfSgn3_10, kbfSgn3_11, kbfSgn3_12]
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  · show ((laplacian kbfSgnPath3Adj).mulVec (![1, 2, 3] : Fin 3 → ℝ)) 2
        = (0 : Fin 3 → ℝ) 2
    rw [laplacian_mulVec_apply, Fin.sum_univ_three, kbfSgn3_20, kbfSgn3_21, kbfSgn3_22]
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num

theorem kbfSgn3_ones_in_kernel :
    (laplacian kbfSgnPath3Adj).mulVec (onesVec : Fin 3 → ℝ) = 0 :=
  laplacian_mulVec_const kbfSgnPath3Adj 1

theorem kbfSgn3_linearIndependent :
    LinearIndependent (R := ℝ) (M := Fin 3 → ℝ)
      (![(onesVec : Fin 3 → ℝ), (![1, 2, 3] : Fin 3 → ℝ)]) := by
  rw [LinearIndependent.pair_iff'
    (by intro h
        have := congrFun h 0
        simp [onesVec] at this)]
  intro a ha
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp only [onesVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one] at h0 h1
  linarith

theorem kbfSgn3_finrank_ker_ge_two :
    2 ≤ Module.finrank ℝ
      (LinearMap.ker (Matrix.mulVecLin (laplacian kbfSgnPath3Adj))) := by
  have hspan : Submodule.span ℝ
      (Set.range (![(onesVec : Fin 3 → ℝ), ![1, 2, 3]]))
      ≤ LinearMap.ker (Matrix.mulVecLin (laplacian kbfSgnPath3Adj)) := by
    rw [Submodule.span_le]
    rintro x hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · show Matrix.mulVecLin (laplacian kbfSgnPath3Adj) onesVec = 0
      rw [Matrix.mulVecLin_apply]
      exact kbfSgn3_ones_in_kernel
    · show Matrix.mulVecLin (laplacian kbfSgnPath3Adj) (![1, 2, 3] : Fin 3 → ℝ) = 0
      rw [Matrix.mulVecLin_apply]
      exact kbfSgn3_kernel_vec
  calc 2 = Fintype.card (Fin 2) := rfl
    _ = Module.finrank ℝ
          (Submodule.span ℝ (Set.range (![(onesVec : Fin 3 → ℝ), ![1, 2, 3]]))) :=
          (finrank_span_eq_card kbfSgn3_linearIndependent).symm
    _ ≤ Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (laplacian kbfSgnPath3Adj))) :=
          Submodule.finrank_mono hspan

/-- **Fence (pos-weight engine, `hnonneg`, the mechanism level):**
`0 < A 0 1` genuine, `L *ᵥ ![1, 2, 3] = 0` genuine, yet the kernel
vector is not constant across the positive edge — the termwise
-vanishing step of the Dirichlet identity is exactly where
nonnegativity enters. -/
theorem kbfSgn3_pos_weight_fence_QA :
    (laplacian kbfSgnPath3Adj).mulVec (![1, 2, 3] : Fin 3 → ℝ) = 0 ∧
      0 < kbfSgnPath3Adj 0 1 ∧
      ¬ ((![1, 2, 3] : Fin 3 → ℝ) 0 = (![1, 2, 3] : Fin 3 → ℝ) 1) :=
  ⟨kbfSgn3_kernel_vec, by rw [kbfSgn3_01]; norm_num, by
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num⟩

/-- **Fence (walk level, `hnonneg`):** the same kernel vector with an
explicit support walk `0 → 1` (witnessed by `kbfSgn3_walk01` through
reachability) refutes `eq_of_supportGraph_walk`'s dropped-`hnonneg`
statement. -/
theorem kbfSgn3_walk_fence_QA :
    (laplacian kbfSgnPath3Adj).mulVec (![1, 2, 3] : Fin 3 → ℝ) = 0 ∧
      (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Reachable 0 1 ∧
      ¬ ((![1, 2, 3] : Fin 3 → ℝ) 0 = (![1, 2, 3] : Fin 3 → ℝ) 1) :=
  ⟨kbfSgn3_kernel_vec, ⟨kbfSgn3_walk01⟩, by
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num⟩

/-- **Fence (iff, → direction):** the dropped-`hnonneg`
`laplacian_mulVec_eq_zero_iff_forall_reachable` fails the other way
here — a genuine kernel vector while the support is connected and the
vector is not constant on it. -/
theorem kbfSgn3_iff_right_fence_QA :
    ¬ ((laplacian kbfSgnPath3Adj).mulVec (![1, 2, 3] : Fin 3 → ℝ) = 0 →
        ∀ i j : Fin 3,
          (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Reachable i j →
            (![1, 2, 3] : Fin 3 → ℝ) i = (![1, 2, 3] : Fin 3 → ℝ) j) := by
  intro h
  have h01 := h kbfSgn3_kernel_vec 0 1 ⟨kbfSgn3_walk01⟩
  simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h01
  norm_num at h01

/-- **Fence (span form, `hnonneg`; `hconn` genuine):** a kernel vector
of a connected-support weighted graph outside the constant line. -/
theorem kbfSgn3_span_fence_QA :
    (![1, 2, 3] : Fin 3 → ℝ)
        ∈ LinearMap.ker (Matrix.mulVecLin (laplacian kbfSgnPath3Adj)) ∧
      (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Connected ∧
      ¬ ((![1, 2, 3] : Fin 3 → ℝ)
          ∈ Submodule.span ℝ ({onesVec} : Set (Fin 3 → ℝ))) :=
  ⟨by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact kbfSgn3_kernel_vec,
    kbfSgnPath3_supportGraph_connected, by
    intro h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨a, ha⟩ := h
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp only [onesVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one] at h0 h1
    norm_num at h0 h1
    linarith⟩

/-- **Fence (exists-const iff, `hnonneg`; `hconn` genuine):** the same
witness — a kernel vector that is not constant. -/
theorem kbfSgn3_exists_const_fence_QA :
    (laplacian kbfSgnPath3Adj).mulVec (![1, 2, 3] : Fin 3 → ℝ) = 0 ∧
      ¬ (∃ c : ℝ, (![1, 2, 3] : Fin 3 → ℝ) = fun _ => c) :=
  ⟨kbfSgn3_kernel_vec, by
    rintro ⟨c, hc⟩
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h0 h1
    linarith⟩

/-- **Fence (bridge, connected orientation):** the dropped-`hnonneg`
kernel-equality bridge separates the other way here — `![1, 2, 3]` is
in the *weighted* kernel but not in the support graph's `lapMatrix`
kernel (whose vectors are constant on the connected support). -/
theorem kbfSgn3_bridge_fence_QA :
    ¬ (LinearMap.ker (Matrix.mulVecLin (laplacian kbfSgnPath3Adj))
        = LinearMap.ker (Matrix.toLin'
            ((supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).lapMatrix ℝ))) := by
  intro h
  have hmem : (![1, 2, 3] : Fin 3 → ℝ)
      ∈ LinearMap.ker (Matrix.mulVecLin (laplacian kbfSgnPath3Adj)) := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact kbfSgn3_kernel_vec
  rw [h] at hmem
  have himpl : ∀ g : Fin 3 → ℝ,
      Matrix.toLin'
          ((supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).lapMatrix ℝ) g = 0 ↔
        ∀ i j : Fin 3,
          (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Reachable i j → g i = g j :=
    (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable
  rw [LinearMap.mem_ker, himpl] at hmem
  have h01 := hmem 0 1 ⟨kbfSgn3_walk01⟩
  simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h01
  norm_num at h01

/-- **Fence (component count, second witness):** the dropped-`hnonneg`
dimension statement fails at connected support too — the weighted
kernel has dimension `≥ 2` against `1` component. -/
theorem kbfSgn3_finrank_fence_QA :
    ¬ (Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (laplacian kbfSgnPath3Adj)))
        = Fintype.card
            (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).ConnectedComponent) := by
  intro h
  have h2 := kbfSgn3_finrank_ker_ge_two
  rw [kbfSgnPath3_card_components_eq_one] at h
  omega

/-! ### Fixture γ: the asymmetric sink star `!![0, 1, 1; 0, 0, 0; 0, 0, 0]]` on `Fin 3` -/

/-- The asymmetric sink-star fixture: one source vertex `0` pointing
at the sinks `1, 2` — *nonnegative* (only `hA` fails), with vacuous
sink rows making the kernel a plane. -/
def kbfAsymSinkAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 1; 0, 0, 0; 0, 0, 0]

theorem kbfA_00 : kbfAsymSinkAdj 0 0 = 0 := rfl
theorem kbfA_01 : kbfAsymSinkAdj 0 1 = 1 := rfl
theorem kbfA_02 : kbfAsymSinkAdj 0 2 = 1 := rfl
theorem kbfA_10 : kbfAsymSinkAdj 1 0 = 0 := rfl
theorem kbfA_11 : kbfAsymSinkAdj 1 1 = 0 := rfl
theorem kbfA_12 : kbfAsymSinkAdj 1 2 = 0 := rfl
theorem kbfA_20 : kbfAsymSinkAdj 2 0 = 0 := rfl
theorem kbfA_21 : kbfAsymSinkAdj 2 1 = 0 := rfl
theorem kbfA_22 : kbfAsymSinkAdj 2 2 = 0 := rfl

/-- **Isolation:** every entry is nonnegative — only symmetry fails. -/
theorem kbfAsymSinkAdj_nonneg : ∀ i j : Fin 3, 0 ≤ kbfAsymSinkAdj i j := by
  intro i j
  have h : kbfAsymSinkAdj i j = 0 ∨ kbfAsymSinkAdj i j = 1 := by
    fin_cases i <;> fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases h with h | h <;> simp [h]

theorem kbfAsymSinkAdj_not_isSymm : ¬ kbfAsymSinkAdj.IsSymm := by
  intro h
  have h10 := Matrix.IsSymm.ext_iff.1 h 1 0
  rw [kbfA_10, kbfA_01] at h10
  norm_num at h10

theorem kbfAsymSink_01_pos : 0 < kbfAsymSinkAdj 0 1 := by
  rw [kbfA_01]
  norm_num

theorem kbfAsymSink_kernel_vec :
    (laplacian kbfAsymSinkAdj).mulVec (![1, 2, 0] : Fin 3 → ℝ) = 0 := by
  funext i
  fin_cases i
  · show ((laplacian kbfAsymSinkAdj).mulVec (![1, 2, 0] : Fin 3 → ℝ)) 0
        = (0 : Fin 3 → ℝ) 0
    rw [laplacian_mulVec_apply, Fin.sum_univ_three, kbfA_00, kbfA_01, kbfA_02]
    simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  · show ((laplacian kbfAsymSinkAdj).mulVec (![1, 2, 0] : Fin 3 → ℝ)) 1
        = (0 : Fin 3 → ℝ) 1
    rw [laplacian_mulVec_apply, Fin.sum_univ_three, kbfA_10, kbfA_11, kbfA_12]
    norm_num
  · show ((laplacian kbfAsymSinkAdj).mulVec (![1, 2, 0] : Fin 3 → ℝ)) 2
        = (0 : Fin 3 → ℝ) 2
    rw [laplacian_mulVec_apply, Fin.sum_univ_three, kbfA_20, kbfA_21, kbfA_22]
    norm_num

/-- **Fence (pos-weight engine, `hA`):** the family's only
`supportGraph`-free statement — `hA` is proof-internal (consumed by
`laplacian_quadForm`), so the dropped-`hA` statement is well-formed.
Every other hypothesis is genuine here (`hnonneg` entrywise, the
kernel equation at `![1, 2, 0]`, `0 < A 0 1`), and the conclusion
`f 0 = f 1` fails: symmetry is load-bearing at the quadratic-form
step, not merely at the `supportGraph` display. -/
theorem kbfAsymSink_pos_weight_hA_fence_QA :
    (∀ i j : Fin 3, 0 ≤ kbfAsymSinkAdj i j) ∧
      ¬ kbfAsymSinkAdj.IsSymm ∧
      (laplacian kbfAsymSinkAdj).mulVec (![1, 2, 0] : Fin 3 → ℝ) = 0 ∧
      0 < kbfAsymSinkAdj 0 1 ∧
      ¬ ((![1, 2, 0] : Fin 3 → ℝ) 0 = (![1, 2, 0] : Fin 3 → ℝ) 1) :=
  ⟨kbfAsymSinkAdj_nonneg, kbfAsymSinkAdj_not_isSymm, kbfAsymSink_kernel_vec,
    kbfAsymSink_01_pos, by
      simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
      norm_num⟩

end BridgeFences

end SpectralGraphTheory.QA
