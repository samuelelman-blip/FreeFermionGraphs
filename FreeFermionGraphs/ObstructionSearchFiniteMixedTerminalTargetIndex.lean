import FreeFermionGraphs.ObstructionSearchFiniteMixedPaperLemma14

/-!
# Canonical terminal target indices

The nearest-target rule already determines the unique index of an obstruction
target on its terminal path.  This module removes that index and its evaluation
equality from the literal tether boundary: both are reconstructed from
`InitializationNearestTargetData`.
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

/-- The canonical terminal-path index of an obstruction target, selected from
the literal nearest-target rule. -/
noncomputable def terminalTargetIndex
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Fin (T.terminalPath target).card :=
  Classical.choose (T.nearestTarget.obstruction_nearest incoming)

/-- The canonical target index evaluates to the obstruction target. -/
theorem terminalTargetIndex_target_eq
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    (T.terminalPath target).vertex (T.terminalTargetIndex incoming) =
      (target : V) :=
  (Classical.choose_spec
    (T.nearestTarget.obstruction_nearest incoming)).1

/-- The canonical target index satisfies the literal nearest-target predicate. -/
theorem terminalTargetIndex_isNearest
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    (T.terminalPath target).IsNearestFrom
      (T.currentSlot source target)
      (I.allowedVertices source)
      (T.terminalTargetIndex incoming) :=
  (Classical.choose_spec
    (T.nearestTarget.obstruction_nearest incoming)).2

/-- Incoming searches with a common obstruction target select the same indexed
vertex of the shared terminal path. -/
theorem terminalTargetIndex_eq
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source source' target : I.Node}
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) :
    T.terminalTargetIndex incoming = T.terminalTargetIndex incoming' := by
  apply (T.terminalPath target).injective
  exact (T.terminalTargetIndex_target_eq incoming).trans
    (T.terminalTargetIndex_target_eq incoming').symm

end InitializationFiniteMixedSideTerminalCoreData

/-- One-sided tether data with the target index removed from the input.  The
index is the canonical one derived from the nearest-target rule. -/
structure FiniteMixedSideIncomingTerminalTetherWithoutTargetIndex
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) : Type where
  targetIndex_even : Even (T.terminalTargetIndex incoming).val
  pathCard_odd : Odd (T.terminalPath target).card
  positive_finalDegree_three :
    ∀ hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount,
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole.externalDegree (target : V) = 3
  clone_adj_flank :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      ∀ q : Fin (T.terminalPath target).card,
        match T.currentSlot source target with
        | .first =>
            q.val + 2 = (T.terminalTargetIndex incoming).val →
              G.Adj X.center ((T.terminalPath target).vertex q)
        | .last =>
            (T.terminalTargetIndex incoming).val + 2 = q.val →
              G.Adj X.center ((T.terminalPath target).vertex q)

namespace FiniteMixedSideIncomingTerminalTetherWithoutTargetIndex

/-- Reconstruct the previous tether interface, deriving both target-index
fields rather than storing them. -/
noncomputable def toIncomingTerminalTether
    {T : I.InitializationFiniteMixedSideTerminalCoreData}
    {source target : I.Node}
    {incoming : I.graph.Arc source target}
    (X : FiniteMixedSideIncomingTerminalTetherWithoutTargetIndex
      T source target incoming) :
    FiniteMixedSideIncomingTerminalTether T source target incoming where
  targetIndex := T.terminalTargetIndex incoming
  target_eq := T.terminalTargetIndex_target_eq incoming
  targetIndex_even := X.targetIndex_even
  pathCard_odd := X.pathCard_odd
  positive_finalDegree_three := X.positive_finalDegree_three
  clone_adj_flank := X.clone_adj_flank

end FiniteMixedSideIncomingTerminalTetherWithoutTargetIndex

/-- Literal tether data for all obstruction arcs, with target indices derived
from the terminal core. -/
structure FiniteMixedSideInitializationTerminalTetherWithoutTargetIndexData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  tether : ∀ ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingTerminalTetherWithoutTargetIndex
        T source target incoming

namespace FiniteMixedSideInitializationTerminalTetherWithoutTargetIndexData

/-- Convert the reduced literal data to the established tether analysis. -/
noncomputable def toTerminalTetherData
    {T : I.InitializationFiniteMixedSideTerminalCoreData}
    (D : FiniteMixedSideInitializationTerminalTetherWithoutTargetIndexData T) :
    FiniteMixedSideInitializationTerminalTetherData T where
  tether := fun incoming =>
    (D.tether incoming).toIncomingTerminalTether

end FiniteMixedSideInitializationTerminalTetherWithoutTargetIndexData

/-- Complete finite terminal data after removing the duplicated target index
and target evaluation certificate. -/
structure InitializationFiniteMixedSideLiteralTerminalWithoutTargetIndexData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  tether : FiniteMixedSideInitializationTerminalTetherWithoutTargetIndexData T
  distinctPropagation : ∀ hclaw : G.IsClawFree,
    FiniteMixedSideDistinctCenterPropagationTraceData T
      tether.toTerminalTetherData hclaw

namespace InitializationFiniteMixedSideLiteralTerminalWithoutTargetIndexData

/-- Exact manuscript Lemma 14 from the reduced finite terminal interface. -/
theorem paperLemma14
    {T : I.InitializationFiniteMixedSideTerminalCoreData}
    (L : InitializationFiniteMixedSideLiteralTerminalWithoutTargetIndexData T)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I := by
  let D := L.tether.toTerminalTetherData
  exact D.paperLemma14_of_distinctCenterConsequences hclaw
    (L.distinctPropagation hclaw).toDistinctCenterConsequences

end InitializationFiniteMixedSideLiteralTerminalWithoutTargetIndexData

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
