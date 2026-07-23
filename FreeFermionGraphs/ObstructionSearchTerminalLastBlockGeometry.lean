import FreeFermionGraphs.ObstructionSearchTerminalDegreeThreeClone

/-!
# Lemma 14(iv): the positive terminal hole is the last block final hole

For a nonempty initialized obstruction-search execution, the manuscript terminal
hole `C_j^(m)` is the final hole of the last ordered Definition 19 block.  The
remaining tether argument is naturally stated on that concrete last block.

This module makes that stage identification explicit and reduces the scoped
terminal-clone interface to the two manuscript geometry facts on the last block:
the obstruction target is outside its final hole and has external degree three.
No terminal-history conclusion is added as data.
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

namespace OrderedOSExecution

/-- The final ordered block index of a positive-length execution. -/
def lastBlockIndex
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount) : Fin X.blockCount :=
  ⟨X.blockCount - 1, by omega⟩

/-- For a positive execution, the manuscript terminal hole is definitionally
represented by the final hole of the last concrete ordered block. -/
theorem manuscriptFinalHole_eq_lastBlockFinalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount) :
    X.manuscriptFinalHole =
      (X.concreteBlock (X.lastBlockIndex hpos)).finalHole := by
  simpa [lastBlockIndex] using X.manuscriptFinalHole_eq_last_of_pos hpos

end OrderedOSExecution

namespace InitializationTerminalCoreData

/-- The two terminal-geometry facts on the concrete last block imply the staged
final-hole clone witness for the incoming arc. -/
theorem exists_terminalCloneWitness_of_lastBlock_geometry
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hpos : 0 < (T.executionTrace.execution source).blockCount)
    (houtside :
      (target : V) ∉ Set.range
        ((T.executionTrace.execution source).concreteBlock
          ((T.executionTrace.execution source).lastBlockIndex hpos)).finalHole.vertex)
    (hthree :
      ((T.executionTrace.execution source).concreteBlock
          ((T.executionTrace.execution source).lastBlockIndex hpos)).finalHole.externalDegree
        (target : V) = 3) :
    Nonempty (IncomingTerminalCloneWitness T source target incoming) := by
  have hfinal :=
    (T.executionTrace.execution source).
      manuscriptFinalHole_eq_lastBlockFinalHole hpos
  apply T.exists_terminalCloneWitness_of_finalHole_externalDegree_eq_three
    hclaw incoming
  · rw [hfinal]
    exact houtside
  · rw [hfinal]
    exact hthree

/-- Exact remaining conditional bridge for the manuscript-scoped interior clone
interface.  Empty executions are handled by the stopping branch; for a positive
execution it is enough to prove the outside-hole and degree-three facts on its
last concrete block from the terminal tether history. -/
theorem interiorTerminalCloneData_of_positive_lastBlock_geometry
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (hgeometry :
      ∀ ⦃source target : I.Node⦄
        (incoming : I.graph.Arc source target),
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source target) ≠ (target : V) →
        ∀ hpos : 0 < (T.executionTrace.execution source).blockCount,
          (target : V) ∉ Set.range
              ((T.executionTrace.execution source).concreteBlock
                ((T.executionTrace.execution source).lastBlockIndex hpos)).finalHole.vertex ∧
            ((T.executionTrace.execution source).concreteBlock
                ((T.executionTrace.execution source).lastBlockIndex hpos)).finalHole.externalDegree
              (target : V) = 3) :
    InitializationInteriorTerminalCloneData T := by
  refine { exists_witness := ?_ }
  intro source target incoming hinterior
  rcases T.terminalCloneWitness_or_blockCount_pos hclaw incoming with
    hwitness | hpos
  · exact hwitness
  · rcases hgeometry incoming hinterior hpos with ⟨houtside, hthree⟩
    exact T.exists_terminalCloneWitness_of_lastBlock_geometry
      hclaw incoming hpos houtside hthree

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
