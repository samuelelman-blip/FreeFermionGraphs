import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalInteriorIndex
import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalCloneFromStopping
import FreeFermionGraphs.Lemma11AThreeNeighborClone

/-!
# Final-hole clones for finite mixed-side terminal executions

The common obstruction target needs a clone witness only in the two-incoming
interior branch of Lemma 14(iv).  This module scopes that witness correctly,
derives the empty-execution case from the literal stopping branch, and reduces
the positive-execution case to the two manuscript facts on the last block's
final hole: the target is outside the hole and has external degree three.

Equality of clone centres is independent of witness choice.  The remaining
branch consequences are kept separate from clone existence.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace FiniteMixedSideIncomingTerminalCloneWitness

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Two final-hole clone witnesses for one incoming finite search select the
same clone index. -/
theorem cloneIndex_eq
    (X Y : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming) :
    X.cloneIndex = Y.cloneIndex :=
  X.target_clone.center_eq Y.target_clone

/-- Hence the displayed centre is independent of the chosen witness. -/
theorem center_eq
    (X Y : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming) :
    X.center = Y.center := by
  unfold center
  rw [X.cloneIndex_eq Y]

end FiniteMixedSideIncomingTerminalCloneWitness

/-- Final-hole clone existence scoped exactly to the manuscript's interior
endpoint alternative. -/
structure FiniteMixedSideInitializationInteriorTerminalCloneData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  exists_witness :
    ∀ ⦃source target : I.Node⦄
      (incoming : I.graph.Arc source target),
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
        Nonempty
          (FiniteMixedSideIncomingTerminalCloneWitness
            T source target incoming)

namespace FiniteMixedSideInitializationInteriorTerminalCloneData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Select the target's final-hole clone witness under the interior premise. -/
noncomputable def witnessOfInterior
    (C : FiniteMixedSideInitializationInteriorTerminalCloneData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hinterior :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V)) :
    FiniteMixedSideIncomingTerminalCloneWitness T source target incoming :=
  Classical.choice (C.exists_witness incoming hinterior)

/-- The selected final-hole clone centre. -/
noncomputable def centerOfInterior
    (C : FiniteMixedSideInitializationInteriorTerminalCloneData T)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hinterior :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V)) : V :=
  (C.witnessOfInterior incoming hinterior).center

/-- Every supplied witness agrees with the selected centre. -/
theorem center_eq_centerOfInterior
    (C : FiniteMixedSideInitializationInteriorTerminalCloneData T)
    {source target : I.Node}
    {incoming : I.graph.Arc source target}
    (hinterior :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V))
    (X : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming) :
    X.center = C.centerOfInterior incoming hinterior :=
  X.center_eq (C.witnessOfInterior incoming hinterior)

end FiniteMixedSideInitializationInteriorTerminalCloneData

/-- The equal-centre and unequal-centre consequences after final-hole clone
existence has been established for the two interior incoming searches. -/
structure FiniteMixedSideTwoIncomingTerminalInteriorCloneConsequences
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (C : FiniteMixedSideInitializationInteriorTerminalCloneData T) : Prop where
  terminalGeometry :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target)
      (hsource :
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source target) ≠ (target : V))
      (hsource' :
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source' target) ≠ (target : V)),
        (C.centerOfInterior incoming hsource =
            C.centerOfInterior incoming' hsource' →
          Nonempty
            ((T.terminalPath target).SameCloneTerminalNeighborhood
              (target : V))) ∧
        (C.centerOfInterior incoming hsource ≠
            C.centerOfInterior incoming' hsource' →
          (Nonempty
              (FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
                T source target incoming) ∨
            Nonempty
              (FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
                T source' target incoming')))

namespace FiniteMixedSideInitializationInteriorTerminalCloneData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Combine scoped final-hole clone existence with the two branch consequences
to recover the staged clone-comparison interface. -/
noncomputable def toTerminalCloneComparisonAnalysis
    (C : FiniteMixedSideInitializationInteriorTerminalCloneData T)
    (A : FiniteMixedSideTwoIncomingTerminalInteriorCloneConsequences T C) :
    FiniteMixedSideTwoIncomingTerminalCloneComparisonAnalysis T where
  terminalGeometry := by
    classical
    intro source source' target hne incoming incoming' hsource hsource'
    let left := C.witnessOfInterior incoming hsource
    let right := C.witnessOfInterior incoming' hsource'
    obtain ⟨hsame, hdistinct⟩ :=
      A.terminalGeometry hne incoming incoming' hsource hsource'
    refine ⟨left, right, ?_, ?_⟩
    · intro hcenter
      apply hsame
      simpa [left, right, centerOfInterior] using hcenter
    · intro hcenter
      apply hdistinct
      simpa [left, right, centerOfInterior] using hcenter

end FiniteMixedSideInitializationInteriorTerminalCloneData

namespace FiniteMixedSideOrderedOSExecution

/-- The final block index of a positive literal finite execution. -/
def lastBlockIndex
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount) : Fin X.blockCount :=
  ⟨X.blockCount - 1, by omega⟩

/-- For a positive execution, the manuscript terminal hole is the final hole
of its last concrete block. -/
theorem manuscriptFinalHole_eq_lastBlockFinalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount) :
    X.manuscriptFinalHole =
      (X.block (X.lastBlockIndex hpos)).finalHole := by
  simpa [lastBlockIndex] using X.manuscriptFinalHole_eq_last_of_pos hpos

end FiniteMixedSideOrderedOSExecution

namespace InitializationFiniteMixedSideTerminalCoreData

/-- An empty finite execution retains the initialized original hole, where the
literal stopping branch already supplies the target clone. -/
theorem exists_terminalCloneWitness_of_blockCount_eq_zero
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hzero :
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount = 0) :
    Nonempty
      (FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming) := by
  obtain ⟨i, hi⟩ := T.exists_target_clone_of_incoming hclaw incoming
  let X :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered source
  have hfinal : X.manuscriptFinalHole =
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole :=
    X.manuscriptFinalHole_eq_original_of_blockCount_eq_zero hzero
  have hwitness :
      ∃ j : Fin X.manuscriptFinalHole.card,
        X.manuscriptFinalHole.SingleVertexDeformation (target : V) j := by
    rw [hfinal]
    exact ⟨i, hi⟩
  obtain ⟨j, hj⟩ := hwitness
  exact ⟨{ cloneIndex := j, target_clone := hj }⟩

/-- Every incoming finite search either has the empty-execution final-hole clone
already, or has positive block count. -/
theorem terminalCloneWitness_or_blockCount_pos
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Nonempty
        (FiniteMixedSideIncomingTerminalCloneWitness
          T source target incoming) ∨
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount := by
  let X :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered source
  by_cases hzero : X.blockCount = 0
  · exact Or.inl
      (T.exists_terminalCloneWitness_of_blockCount_eq_zero
        hclaw incoming hzero)
  · exact Or.inr (Nat.pos_of_ne_zero hzero)

/-- Outside the correctly staged finite final hole, external degree three gives
a clone witness by the claw-free three-neighbour theorem. -/
theorem exists_terminalCloneWitness_of_finalHole_externalDegree_eq_three
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (houtside :
      (target : V) ∉ Set.range
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).manuscriptFinalHole.vertex)
    (hthree :
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole.externalDegree (target : V) = 3) :
    Nonempty
      (FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming) := by
  obtain ⟨i, hi⟩ :=
    IndexedInducedHole.exists_singleVertexDeformation_of_externalDegree_eq_three
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole
      hclaw houtside hthree
  exact ⟨{ cloneIndex := i, target_clone := hi }⟩

/-- The two last-block geometry facts imply the final-hole clone witness for a
positive finite execution. -/
theorem exists_terminalCloneWitness_of_lastBlock_geometry
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount)
    (houtside :
      (target : V) ∉ Set.range
        ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).block
            ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
              source).lastBlockIndex hpos)).finalHole.vertex)
    (hthree :
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block
          ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source).lastBlockIndex hpos)).finalHole.externalDegree
        (target : V) = 3) :
    Nonempty
      (FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming) := by
  let X :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered source
  have hfinal := X.manuscriptFinalHole_eq_lastBlockFinalHole hpos
  apply T.exists_terminalCloneWitness_of_finalHole_externalDegree_eq_three
    hclaw incoming
  · rw [hfinal]
    exact houtside
  · rw [hfinal]
    exact hthree

/-- Exact remaining clone-existence bridge: empty executions are solved by the
stopping branch, while positive executions require only outside-hole and
degree-three facts on the concrete last block. -/
theorem interiorTerminalCloneData_of_positive_lastBlock_geometry
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    (hgeometry :
      ∀ ⦃source target : I.Node⦄
        (incoming : I.graph.Arc source target),
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source target) ≠ (target : V) →
        ∀ hpos :
          0 <
            (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
              source).blockCount,
          (target : V) ∉ Set.range
              ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
                source).block
                  ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
                    source).lastBlockIndex hpos)).finalHole.vertex ∧
            ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
              source).block
                ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
                  source).lastBlockIndex hpos)).finalHole.externalDegree
              (target : V) = 3) :
    FiniteMixedSideInitializationInteriorTerminalCloneData T := by
  refine { exists_witness := ?_ }
  intro source target incoming hinterior
  rcases T.terminalCloneWitness_or_blockCount_pos hclaw incoming with
    hwitness | hpos
  · exact hwitness
  · rcases hgeometry incoming hinterior hpos with ⟨houtside, hthree⟩
    exact T.exists_terminalCloneWitness_of_lastBlock_geometry
      hclaw incoming hpos houtside hthree

/-- Conditional paper-facing Lemma 14 bridge once finite final-hole clone
existence and the equal/distinct-centre consequences have been constructed. -/
theorem paperLemma14_of_interiorTerminalCloneData_and_consequences
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (C : FiniteMixedSideInitializationInteriorTerminalCloneData T)
    (A : FiniteMixedSideTwoIncomingTerminalInteriorCloneConsequences T C)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I :=
  T.paperLemma14_of_terminalCloneComparisonAnalysis
    (C.toTerminalCloneComparisonAnalysis A) hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
