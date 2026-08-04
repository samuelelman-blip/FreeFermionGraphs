import FreeFermionGraphs.ObstructionSearchFiniteMixedGeneratedTerminalEvent
import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalDegreeFromCommutation

/-!
# Terminal stopping events from commuting finite executions

The manuscript does not assume step-by-step target balance.  In the remaining
interior branch it proves that the common obstruction target commutes with every
path component in each incoming search.  The parity argument in
`ObstructionSearchFiniteMixedTerminalDegreeFromCommutation` then derives degree
three on the exact positive terminal hole.

This module keeps the literal terminal-path and tether-link coordinates, but
replaces the stronger `TargetBalanced` field by commutation with every actual
finite execution path.
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

/-- One incoming terminal stop whose degree invariant is generated from the
manuscript's path-commutation assertion. -/
structure FiniteMixedSideIncomingCommutingTerminalStop
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (P : FiniteMixedSideTerminalPathExecution T target)
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
      | .first => (linkIndex X).val + 1 = P.targetIndex.val
      | .last => P.targetIndex.val + 1 = (linkIndex X).val

namespace FiniteMixedSideIncomingCommutingTerminalStop

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target source : I.Node}
  {incoming : I.graph.Arc source target}
  {P : FiniteMixedSideTerminalPathExecution T target}

/-- Commutation with every actual path gives exact positive terminal degree
three by parity, even-hole geometry, and Lemma 7. -/
theorem positive_finalDegree_three
    (E : FiniteMixedSideIncomingCommutingTerminalStop
      T P source target incoming)
    (hclaw : G.IsClawFree)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.externalDegree (target : V) = 3 :=
  T.positive_finalDegree_three_of_executionPaths_commute
    hclaw incoming E.targetCommutes hpos

/-- The target coordinate chosen by the terminal event is the canonical
nearest-target index. -/
theorem targetIndex_eq_canonical
    (E : FiniteMixedSideIncomingCommutingTerminalStop
      T P source target incoming) :
    P.targetIndex = T.terminalTargetIndex incoming := by
  apply (T.terminalPath target).injective
  exact P.targetIndex_target_eq.trans
    (T.terminalTargetIndex_target_eq incoming).symm

/-- The adjacent tether-link coordinate gives the staged clone-to-flank
adjacency. -/
theorem clone_adj_flank
    (E : FiniteMixedSideIncomingCommutingTerminalStop
      T P source target incoming)
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
  have htarget := E.targetIndex_eq_canonical
  cases hs : T.currentSlot source target with
  | first =>
      intro hq
      have hr := E.link_toward_target X
      have hr' : r.val + 1 = P.targetIndex.val := by
        simpa [hs, r] using hr
      rw [← hcenter]
      apply ((T.terminalPath target).adj_iff r q).2
      right
      rw [← htarget] at hq
      omega
  | last =>
      intro hq
      have hr := E.link_toward_target X
      have hr' : P.targetIndex.val + 1 = r.val := by
        simpa [hs, r] using hr
      rw [← hcenter]
      apply ((T.terminalPath target).adj_iff r q).2
      left
      rw [← htarget] at hq
      omega

/-- Convert the commuting stop to the operational tether interface. -/
def toOperationalTether
    (E : FiniteMixedSideIncomingCommutingTerminalStop
      T P source target incoming)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideIncomingOperationalTether T source target incoming where
  positive_finalDegree_three := E.positive_finalDegree_three hclaw
  clone_adj_flank := E.clone_adj_flank

end FiniteMixedSideIncomingCommutingTerminalStop

/-- Terminal events with degree generated from path commutation rather than a
stepwise adjacency-balance certificate. -/
structure InitializationFiniteMixedSideCommutingTerminalEvent
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  path : ∀ target : I.Node,
    FiniteMixedSideTerminalPathExecution T target
  stop : ∀ ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingCommutingTerminalStop
        T (path target) source target incoming

namespace InitializationFiniteMixedSideCommutingTerminalEvent

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Terminal labels, degree three, and flank adjacency derived from the
commuting terminal event. -/
def toLabelledOperationalTerminalData
    (E : InitializationFiniteMixedSideCommutingTerminalEvent T)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideInitializationLabelledOperationalTerminalData T where
  labels :=
    FiniteMixedSideTerminalPathExecution.toAlternatingLabelData E.path
  tether := fun {source target} incoming =>
    (E.stop (source := source) (target := target) incoming).toOperationalTether
      hclaw

end InitializationFiniteMixedSideCommutingTerminalEvent

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
