import FreeFermionGraphs.ObstructionSearchTwoSidedMixedSideReduction

/-!
# Corollary 11 for mixed-side Definition 19 histories

A hypothetical shared dependent anticommuting witness first forces the earlier
and current path blocks to have the same manuscript component side.  After
reorienting both blocks in that common side, the existing concrete Corollary 11
theorem applies on the original hole of the literal mixed history.

The carrier sequence itself remains unswapped.  Only the local colour data are
read in the selected orientation.  No obstruction-search execution is
constructed here, and no conclusion of Lemma 14 is assumed.
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

namespace MixedSideFullDefinition19Lemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}

/-- Corollary 11 for an earlier block and the current block of a positive
mixed-side Definition 19 history. -/
theorem noSharedDependentAnticommutingWitness_of_mixedSideHistory
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {r : Nat} (hr : r < X.priorCount) :
    ¬SharedDependentAnticommutingWitness
      (X.history.carrier.block r).path D.path
      (X.history.carrier.block r).dependentAt D.dependentAt := by
  intro hshared
  have hside : X.history.side r = X.currentSide :=
    X.priorSide_eq_currentSide_of_sharedDependentAnticommutingWitness
      r hshared
  cases hside
  let C : IndexedInducedHole G := X.originalHole
  have hEvenCarrier :
      Even (X.history.carrier.block 0).initialHole.card := by
    apply even_initialHole_of_reorient
      (X.history.carrier.block 0) (X.history.side 0)
    simpa [MixedSidePathBlockHistory.orientedBlock] using
      (X.history.localData 0).neighborhood.alternating.initialHole_even
  have hEven : Even C.card := by
    simpa [C, originalHole] using hEvenCarrier
  have hcarrierOriginal : Set.range C.vertex ⊆ O.Ca ∪ O.Cb := by
    intro x hx
    let A0 := X.history.orientedBlock 0
    have hxCarrierInitial :
        x ∈ Set.range (X.history.carrier.block 0).initialHole.vertex := by
      simpa [C, originalHole] using hx
    have hxOrientedInitial : x ∈ Set.range A0.initialHole.vertex := by
      simpa [A0, MixedSidePathBlockHistory.orientedBlock] using
        (mem_reorient_initialHole_of_mem_initialHole
          (X.history.carrier.block 0) (X.history.side 0)
          hxCarrierInitial)
    have hxBefore :
        x ∈ Set.range
          (A0.deformation.step A0.firstIndex).before.vertex := by
      simpa [ConcretePathDeformation.initialHole] using hxOrientedInitial
    have hxSelected :
        x ∈ ((X.history.side 0).family O).Ca ∪
          ((X.history.side 0).family O).Cb := by
      exact
        ((X.history.localData 0).neighborhood.mechanical.stepGeometry
          A0.firstIndex).before_subset hxBefore
    exact mem_original_colors_of_mem_oriented_colors
      (X.history.side 0) hxSelected
  have hcarrier :
      Set.range C.vertex ⊆
        (X.currentSide.family O).Ca ∪ (X.currentSide.family O).Cb := by
    intro x hx
    exact mem_oriented_colors_of_mem_original_colors
      X.currentSide (hcarrierOriginal hx)
  have hpathNe :
      Set.range (X.history.orientedBlock r).path.vertex ≠
        Set.range X.orientedCurrent.path.vertex := by
    simpa only [X.history.orientedBlock_path r,
      X.orientedCurrent_path] using X.priorPath_ne_current r hr
  have hcommonPrior :
      (X.currentSide.family O).BaseCommonNeighborOn
        (X.history.orientedBlock r) C := by
    simpa [C] using
      D.priorBaseCommonNeighborOn_of_mixedSideHistory X hclaw r
  have hcommonCurrent :
      (X.currentSide.family O).BaseCommonNeighborOn
        X.orientedCurrent C := by
    simpa [C] using
      D.currentBaseCommonNeighborOn_of_mixedSideHistory X hclaw
  have hno :
      ¬SharedDependentAnticommutingWitness
        (X.history.orientedBlock r).path X.orientedCurrent.path
        (X.history.orientedBlock r).dependentAt
        X.orientedCurrent.dependentAt :=
    noSharedDependentAnticommutingWitness_of_concreteBlocks
      (X.history.orientedBlock r) X.orientedCurrent
      (X.history.localData r) X.current C hclaw hEven hcarrier
      hpathNe hcommonPrior hcommonCurrent
  apply hno
  rcases hshared with
    ⟨u, s, t, huPrior, huCurrent, hantiPrior, hantiCurrent⟩
  refine ⟨u, s, t, ?_, ?_, ?_, ?_⟩
  · rw [X.history.orientedBlock_dependentAt r s]
    exact huPrior
  · rw [X.orientedCurrent_dependentAt t]
    exact huCurrent
  · simpa only [X.history.orientedBlock_path r] using hantiPrior
  · simpa only [X.orientedCurrent_path] using hantiCurrent

end MixedSideFullDefinition19Lemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
