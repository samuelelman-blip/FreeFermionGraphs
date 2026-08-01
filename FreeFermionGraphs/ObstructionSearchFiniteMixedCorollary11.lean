import FreeFermionGraphs.ObstructionSearchFiniteMixedCommonNeighbor
import FreeFermionGraphs.Lemma11BEvenness

/-!
# Corollary 11 on bounded mixed-side histories

A shared dependent anticommuting witness first forces an earlier block and the
current block to use the same manuscript component side.  Reorienting both
blocks in that common side lets the concrete Corollary 11 theorem exclude the
witness on the literal original hole.

The argument uses only `FiniteMixedSideLemma11AHistoryData`; no total natural
history and no conclusion of Lemma 11 or Lemma 14 is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem even_initialHole_of_reorient
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (hEven : Even (A.reorient side).initialHole.card) :
    Even A.initialHole.card := by
  cases side <;> exact hEven

private theorem mem_reorient_initialHole_of_mem_initialHole
    (A : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    {x : V}
    (hx : x ∈ Set.range A.initialHole.vertex) :
    x ∈ Set.range (A.reorient side).initialHole.vertex := by
  cases side <;> exact hx

private theorem mem_original_colors_of_mem_oriented_colors
    (side : DeformationSide)
    {x : V}
    (hx : x ∈ (side.family O).Ca ∪ (side.family O).Cb) :
    x ∈ O.Ca ∪ O.Cb := by
  cases side with
  | ac =>
      simpa [DeformationSide.family] using hx
  | bd =>
      simpa [DeformationSide.family, swapSides, Set.union_comm] using hx

private theorem mem_oriented_colors_of_mem_original_colors
    (side : DeformationSide)
    {x : V}
    (hx : x ∈ O.Ca ∪ O.Cb) :
    x ∈ (side.family O).Ca ∪ (side.family O).Cb := by
  cases side with
  | ac =>
      simpa [DeformationSide.family] using hx
  | bd =>
      simpa [DeformationSide.family, swapSides, Set.union_comm] using hx

private theorem baseCommonNeighborOn_reorient_of_side_eq
    (A : ConcretePathDeformation O Cprime)
    (C : IndexedInducedHole G)
    (sideA sideB : DeformationSide)
    (hside : sideA = sideB)
    (hcommon : (sideA.family O).BaseCommonNeighborOn
      (A.reorient sideA) C) :
    (sideB.family O).BaseCommonNeighborOn (A.reorient sideB) C := by
  subst sideB
  exact hcommon

namespace FiniteMixedSideLemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Corollary 11 for an earlier block and the current block of a bounded
mixed-side Definition 19 prefix. -/
theorem noSharedDependentAnticommutingWitness
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    (hclaw : G.IsClawFree)
    (r : Fin H.priorCount) :
    ¬SharedDependentAnticommutingWitness
      (H.priorBlock r).path D.path
      (H.priorBlock r).dependentAt D.dependentAt := by
  intro hshared
  have hside : H.priorSide r = H.currentSide :=
    H.priorSide_eq_currentSide_of_sharedDependentAnticommutingWitness
      r hshared
  let C : IndexedInducedHole G := originalHole
  let A : ConcretePathDeformation (H.currentSide.family O) Cprime :=
    (H.priorBlock r).reorient H.currentSide
  have hPriorData : A.FullDefinition19Lemma11AData := by
    have hData :
        ((H.priorBlock r).reorient
          H.currentSide).FullDefinition19Lemma11AData := by
      rw [← hside]
      exact H.priorData r
    simpa [A] using hData
  let first : Fin H.priorCount := ⟨0, H.priorCount_pos⟩
  have hEvenCarrier :
      Even (H.priorBlock first).initialHole.card := by
    apply even_initialHole_of_reorient
      (H.priorBlock first) (H.priorSide first)
    simpa [orientedPrior] using
      (H.priorData first).neighborhood.alternating.initialHole_even
  have hEven : Even C.card := by
    change Even originalHole.card
    have hcard :
        (H.priorBlock first).initialHole.card = originalHole.card :=
      IndexedInducedHole.card_eq_of_range_eq
        (H.priorBlock first).initialHole originalHole (by
          simpa [first] using H.firstInitial_eq_original)
    rw [← hcard]
    exact hEvenCarrier
  have hcarrierOriginal : Set.range C.vertex ⊆ O.Ca ∪ O.Cb := by
    intro x hx
    let A0 := H.orientedPrior first
    have hxCarrierInitial :
        x ∈ Set.range (H.priorBlock first).initialHole.vertex := by
      rw [H.firstInitial_eq_original]
      simpa [C] using hx
    have hxOrientedInitial : x ∈ Set.range A0.initialHole.vertex := by
      simpa [A0, orientedPrior] using
        (mem_reorient_initialHole_of_mem_initialHole
          (H.priorBlock first) (H.priorSide first) hxCarrierInitial)
    have hxBefore :
        x ∈ Set.range
          (A0.deformation.step A0.firstIndex).before.vertex := by
      simpa [ConcretePathDeformation.initialHole] using hxOrientedInitial
    have hxSelected :
        x ∈ ((H.priorSide first).family O).Ca ∪
          ((H.priorSide first).family O).Cb :=
      ((H.priorData first).neighborhood.mechanical.stepGeometry
        A0.firstIndex).before_subset hxBefore
    exact mem_original_colors_of_mem_oriented_colors
      (H.priorSide first) hxSelected
  have hcarrier :
      Set.range C.vertex ⊆
        (H.currentSide.family O).Ca ∪
          (H.currentSide.family O).Cb := by
    intro x hx
    exact mem_oriented_colors_of_mem_original_colors
      H.currentSide (hcarrierOriginal hx)
  have hpathNe :
      Set.range A.path.vertex ≠
        Set.range (D.reorient H.currentSide).path.vertex := by
    simpa only [A, ConcretePathDeformation.reorient_path] using
      H.priorPath_ne_current r
  have hcommonPrior :
      (H.currentSide.family O).BaseCommonNeighborOn A C := by
    have hRaw := H.priorBaseCommonNeighborOn hclaw r
    have hTransported := baseCommonNeighborOn_reorient_of_side_eq
      (H.priorBlock r) originalHole
      (H.priorSide r) H.currentSide hside hRaw
    simpa [A, C] using hTransported
  have hcommonCurrent :
      (H.currentSide.family O).BaseCommonNeighborOn
        (D.reorient H.currentSide) C := by
    simpa [C] using H.currentBaseCommonNeighborOn hclaw
  have hno :
      ¬SharedDependentAnticommutingWitness
        A.path (D.reorient H.currentSide).path
        A.dependentAt (D.reorient H.currentSide).dependentAt :=
    noSharedDependentAnticommutingWitness_of_concreteBlocks
      A (D.reorient H.currentSide) hPriorData H.current C hclaw
      hEven hcarrier hpathNe hcommonPrior hcommonCurrent
  apply hno
  rcases hshared with
    ⟨u, s, t, huPrior, huCurrent, hantiPrior, hantiCurrent⟩
  refine ⟨u, s, t, ?_, ?_, ?_, ?_⟩
  · change u ∈
      ((H.priorBlock r).reorient H.currentSide).dependentAt s
    rw [(H.priorBlock r).reorient_dependentAt H.currentSide s]
    exact huPrior
  · rw [D.reorient_dependentAt H.currentSide t]
    exact huCurrent
  · simpa only [A, ConcretePathDeformation.reorient_path] using hantiPrior
  · simpa only [ConcretePathDeformation.reorient_path] using hantiCurrent

end FiniteMixedSideLemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
