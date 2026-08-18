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

end SpectralGraphTheory.QA
