import FreeFermionGraphs.ObstructionSearchFiniteMixedFinalCarrierProvenance

/-!
# Reducing finite terminal clone construction to degree three

Carrier provenance now proves automatically that every obstruction target is
outside the positive manuscript terminal hole.  Consequently the only
remaining positive-execution premise needed to construct the staged clone is
the manuscript degree-three conclusion on that exact final hole.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Empty executions are already solved by the stopping branch.  For a
positive finite execution, final-hole degree three alone constructs the scoped
terminal clone witness. -/
theorem interiorTerminalCloneData_of_positive_finalDegree_three
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    (hthree :
      ∀ ⦃source target : I.Node⦄
        (incoming : I.graph.Arc source target),
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source target) ≠ (target : V) →
        ∀ hpos :
          0 <
            (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
              source).blockCount,
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source).manuscriptFinalHole.externalDegree (target : V) = 3) :
    FiniteMixedSideInitializationInteriorTerminalCloneData T := by
  apply T.interiorTerminalCloneData_of_positive_lastBlock_geometry hclaw
  intro source target incoming hinterior hpos
  let X :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered source
  have hfinal := X.manuscriptFinalHole_eq_lastBlockFinalHole hpos
  constructor
  · rw [← hfinal]
    exact T.target_not_mem_manuscriptFinalHole_of_pos incoming hpos
  · rw [← hfinal]
    exact hthree incoming hinterior hpos

/-- Paper-facing Lemma 14 after the remaining degree-three theorem and the two
clone-centre branch consequences have been established from the terminal
histories. -/
theorem paperLemma14_of_positive_finalDegree_three_and_consequences
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    (hthree :
      ∀ ⦃source target : I.Node⦄
        (incoming : I.graph.Arc source target),
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source target) ≠ (target : V) →
        ∀ hpos :
          0 <
            (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
              source).blockCount,
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source).manuscriptFinalHole.externalDegree (target : V) = 3)
    (A :
      let C := T.interiorTerminalCloneData_of_positive_finalDegree_three
        hclaw hthree
      FiniteMixedSideTwoIncomingTerminalInteriorCloneConsequences T C) :
    PaperLemma14Conclusion I := by
  let C := T.interiorTerminalCloneData_of_positive_finalDegree_three
    hclaw hthree
  exact T.paperLemma14_of_interiorTerminalCloneData_and_consequences
    C (by simpa [C] using A) hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
