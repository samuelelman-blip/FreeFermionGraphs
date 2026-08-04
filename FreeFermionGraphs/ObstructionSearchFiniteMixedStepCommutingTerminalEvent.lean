import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalStepAlternation
import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalDegreeFromCommutation

/-!
# Terminal events from stepwise alternation and path commutation

This module removes the explicit terminal coordinate partition from the
strongest finite Lemma 14 bridge. The terminal path supplies only a colour side
that flips at each step. Global even-index labels are derived from that local
fact. The target's degree three is derived from commutation with every actual
execution path, and the adjacent stopping link is stated against the canonical
nearest-target index.
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

/-- One incoming terminal stop using the canonical nearest-target index.

No explicit `j`/`k` coordinate partition or target-position field is stored.
The degree-three conclusion is derived from commutation with the actual finite
execution paths. -/
structure FiniteMixedSideIncomingCanonicalCommutingStop
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  targetCommutes :
    ∀ q : Fin
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount,
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block q).path.CommutesWith (target : V)
  linkIndex :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      Fin (T.terminalPath target).card
  link_center_eq :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      (T.terminalPath target).vertex (linkIndex X) = X.center
  link_toward_target :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      match T.currentSlot source target with
      | .first =>
          (linkIndex X).val + 1 = (T.terminalTargetIndex incoming).val
      | .last =>
          (T.terminalTargetIndex incoming).val + 1 = (linkIndex X).val

namespace FiniteMixedSideIncomingCanonicalCommutingStop

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Path commutation gives degree three on the exact positive terminal hole. -/
theorem positive_finalDegree_three
    (E : FiniteMixedSideIncomingCanonicalCommutingStop
      T source target incoming)
    (hclaw : G.IsClawFree)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.externalDegree (target : V) = 3 :=
  T.positive_finalDegree_three_of_executionPaths_commute
    hclaw incoming E.targetCommutes hpos

/-- The canonical adjacent stopping link gives clone-to-flank adjacency. -/
theorem clone_adj_flank
    (E : FiniteMixedSideIncomingCanonicalCommutingStop
      T source target incoming)
    (X : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming)
    (q : Fin (T.terminalPath target).card) :
    match T.currentSlot source target with
    | .first =>
        q.val + 2 = (T.terminalTargetIndex incoming).val →
          G.Adj X.center ((T.terminalPath target).vertex q)
    | .last =>
        (T.terminalTargetIndex incoming).val + 2 = q.val →
          G.Adj X.center ((T.terminalPath target).vertex q) := by
  let r := E.linkIndex X
  have hcenter := E.link_center_eq X
  cases hs : T.currentSlot source target with
  | first =>
      intro hq
      have hr := E.link_toward_target X
      have hr' : r.val + 1 = (T.terminalTargetIndex incoming).val := by
        simpa [hs, r] using hr
      rw [← hcenter]
      apply ((T.terminalPath target).adj_iff r q).2
      right
      omega
  | last =>
      intro hq
      have hr := E.link_toward_target X
      have hr' : (T.terminalTargetIndex incoming).val + 1 = r.val := by
        simpa [hs, r] using hr
      rw [← hcenter]
      apply ((T.terminalPath target).adj_iff r q).2
      left
      omega

/-- Convert the canonical commuting stop to the operational tether interface. -/
def toOperationalTether
    (E : FiniteMixedSideIncomingCanonicalCommutingStop
      T source target incoming)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideIncomingOperationalTether T source target incoming where
  positive_finalDegree_three := E.positive_finalDegree_three hclaw
  clone_adj_flank := E.clone_adj_flank

end FiniteMixedSideIncomingCanonicalCommutingStop

/-- Terminal event with local path alternation and canonical stopping links. -/
structure InitializationFiniteMixedSideStepCommutingTerminalEvent
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  alternation : FiniteMixedSideTerminalStepAlternationData T
  stop : ∀ {source target : I.Node}
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingCanonicalCommutingStop
        T source target incoming

namespace InitializationFiniteMixedSideStepCommutingTerminalEvent

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Derive all terminal labels, degree-three facts, and flank adjacencies. -/
def toLabelledOperationalTerminalData
    (E : InitializationFiniteMixedSideStepCommutingTerminalEvent T)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideInitializationLabelledOperationalTerminalData T where
  labels := E.alternation.toAlternatingLabelData
  tether := fun {source target} incoming =>
    (E.stop incoming).toOperationalTether hclaw

end InitializationFiniteMixedSideStepCommutingTerminalEvent

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
