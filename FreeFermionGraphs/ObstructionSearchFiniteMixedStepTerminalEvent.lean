import FreeFermionGraphs.ObstructionSearchFiniteMixedStepCommutingTerminalEvent
import FreeFermionGraphs.ObstructionSearchFiniteMixedTargetCommutationFromClone

/-!
# Terminal events from raw stopping data

The literal terminal stop provides a positive final-hole clone and the adjacent
canonical tether link. Target commutation is not stored: it is derived from the
clone relation, finite Lemma 11(a), Corollary 11, and the parity contradiction.
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

/-- Raw canonical terminal stop.

The fields are literal stopping geometry: a positive execution ends with the
target as a single-vertex deformation of the final hole, and the staged clone
centre lies at the path coordinate adjacent to the canonical target index. -/
structure FiniteMixedSideIncomingCanonicalTerminalStop
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  positive_target_clone :
    ∀ hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount,
      ∃ i : Fin
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source).manuscriptFinalHole.card,
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).manuscriptFinalHole.SingleVertexDeformation
            (target : V) i
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

namespace FiniteMixedSideIncomingCanonicalTerminalStop

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Derive target commutation and construct the canonical commuting stop. -/
def toCommutingStop
    (E : FiniteMixedSideIncomingCanonicalTerminalStop
      T source target incoming)
    (P : I.InitializationPrimeVertexData)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideIncomingCanonicalCommutingStop
      T source target incoming where
  targetCommutes := fun q =>
    T.target_commutes_executionPath_of_positive_target_clone
      P hclaw incoming E.positive_target_clone q
  linkIndex := E.linkIndex
  link_center_eq := E.link_center_eq
  link_toward_target := E.link_toward_target

end FiniteMixedSideIncomingCanonicalTerminalStop

/-- Terminal event with local colour alternation and raw canonical stopping
geometry. -/
structure InitializationFiniteMixedSideStepTerminalEvent
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  alternation : FiniteMixedSideTerminalStepAlternationData T
  stop : ∀ {source target : I.Node}
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingCanonicalTerminalStop
        T source target incoming

namespace InitializationFiniteMixedSideStepTerminalEvent

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Derive target commutation for every incoming stop. -/
def toStepCommutingTerminalEvent
    (E : InitializationFiniteMixedSideStepTerminalEvent T)
    (P : I.InitializationPrimeVertexData)
    (hclaw : G.IsClawFree) :
    InitializationFiniteMixedSideStepCommutingTerminalEvent T where
  alternation := E.alternation
  stop := fun incoming => (E.stop incoming).toCommutingStop P hclaw

/-- Derive the operational terminal interface directly from raw stopping data. -/
def toLabelledOperationalTerminalData
    (E : InitializationFiniteMixedSideStepTerminalEvent T)
    (P : I.InitializationPrimeVertexData)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideInitializationLabelledOperationalTerminalData T :=
  (E.toStepCommutingTerminalEvent P hclaw).toLabelledOperationalTerminalData
    hclaw

end InitializationFiniteMixedSideStepTerminalEvent

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
