import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalTether

/-!
# Selecting the positive execution in the unequal-centre branch

If a literal finite execution has no path blocks, its manuscript final hole is
the initialized original hole.  Clone centres of one target in that fixed hole
are unique.  Consequently two unequal staged clone centres cannot both come
from empty executions, so the distinct-centre branch always supplies at least
one genuinely positive finite history on which the long propagation can run.
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

/-- Two staged clone witnesses in empty executions display the same original-
hole clone centre. -/
theorem terminalClone_center_eq_of_both_blockCount_eq_zero
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source source' target : I.Node}
    {incoming : I.graph.Arc source target}
    {incoming' : I.graph.Arc source' target}
    (left : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming)
    (right : FiniteMixedSideIncomingTerminalCloneWitness
      T source' target incoming')
    (hzero :
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount = 0)
    (hzero' :
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source').blockCount = 0) :
    left.center = right.center := by
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  let C := Y.originalHole
  let X := Y.ordered source
  let X' := Y.ordered source'
  have hfinal : X.manuscriptFinalHole = C :=
    X.manuscriptFinalHole_eq_original_of_blockCount_eq_zero hzero
  have hfinal' : X'.manuscriptFinalHole = C :=
    X'.manuscriptFinalHole_eq_original_of_blockCount_eq_zero hzero'
  have hleft := left.target_clone
  have hright := right.target_clone
  change X.manuscriptFinalHole.SingleVertexDeformation
      (target : V) left.cloneIndex at hleft
  change X'.manuscriptFinalHole.SingleVertexDeformation
      (target : V) right.cloneIndex at hright
  cases hfinal
  cases hfinal'
  have hindex := hleft.center_eq hright
  unfold FiniteMixedSideIncomingTerminalCloneWitness.center
  exact congrArg C.vertex hindex

/-- Unequal staged centres force at least one of the two actual finite
executions to have positive block count. -/
theorem blockCount_pos_or_blockCount_pos_of_terminalClone_center_ne
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source source' target : I.Node}
    {incoming : I.graph.Arc source target}
    {incoming' : I.graph.Arc source' target}
    (left : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming)
    (right : FiniteMixedSideIncomingTerminalCloneWitness
      T source' target incoming')
    (hne : left.center ≠ right.center) :
    0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount ∨
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source').blockCount := by
  by_cases hzero :
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount = 0
  · right
    by_contra hpos'
    have hzero' :
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source').blockCount = 0 := by omega
    exact hne
      (T.terminalClone_center_eq_of_both_blockCount_eq_zero
        left right hzero hzero')
  · left
    exact Nat.pos_of_ne_zero hzero

end InitializationFiniteMixedSideTerminalCoreData

/-- The positive side selected by an unequal pair of terminal clone centres. -/
inductive FiniteMixedSidePositiveDistinctSide
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source source' target : I.Node}
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) : Prop where
  | left
      (hpos :
        0 <
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source).blockCount) :
      FiniteMixedSidePositiveDistinctSide T incoming incoming'
  | right
      (hpos :
        0 <
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source').blockCount) :
      FiniteMixedSidePositiveDistinctSide T incoming incoming'

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Choose one positive execution from an unequal pair of staged clone
centres. -/
theorem positiveDistinctSide_of_terminalClone_center_ne
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source source' target : I.Node}
    {incoming : I.graph.Arc source target}
    {incoming' : I.graph.Arc source' target}
    (left : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming)
    (right : FiniteMixedSideIncomingTerminalCloneWitness
      T source' target incoming')
    (hne : left.center ≠ right.center) :
    FiniteMixedSidePositiveDistinctSide T incoming incoming' := by
  rcases T.blockCount_pos_or_blockCount_pos_of_terminalClone_center_ne
      left right hne with hleft | hright
  · exact FiniteMixedSidePositiveDistinctSide.left hleft
  · exact FiniteMixedSidePositiveDistinctSide.right hright

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
