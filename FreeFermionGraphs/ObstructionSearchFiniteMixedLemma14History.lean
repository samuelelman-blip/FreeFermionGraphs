import FreeFermionGraphs.ObstructionSearchFiniteMixedStepTerminalEvent

/-!
# Lemma 14 from finite obstruction-search histories

The lower-level part of this module packages the modular executable bridge.
The second part defines the literal initialized Definition 19/20 history and
exports the unqualified manuscript theorem.

Terminal parity is derived from local stepwise alternation. Target commutation
is derived from the positive terminal clone, finite Lemma 11(a), Corollary 11,
and parity through the later execution suffix. Commuting blocks preserve degree
parity, and Lemma 7 forces the odd terminal degree to remain three.
Clone-to-flank adjacency is derived from the adjacent canonical stopping link.
Unequal-centre propagation witnesses carry an indexed `IsGenerated` derivation
assembled only by the finite `start` and `snoc` constructors.
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

/-- Generated terminal and propagation data used by the modular bridge. -/
structure InitializationFiniteMixedSideExecutableLemma14Data
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  prime : I.InitializationPrimeVertexData
  terminal : InitializationFiniteMixedSideStepTerminalEvent T
  propagation : ∀ hclaw : G.IsClawFree,
    let terminalData :=
      terminal.toLabelledOperationalTerminalData prime hclaw
    let D := terminalData.toOperationalTerminalData.toTerminalTetherData
    FiniteMixedSideDistinctCenterGeneratedPropagationData T D hclaw

namespace InitializationFiniteMixedSideExecutableLemma14Data

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Modular bridge to the exact four-part conclusion of manuscript Lemma 14. -/
theorem paperLemma14_of_executableData
    (L : InitializationFiniteMixedSideExecutableLemma14Data T)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I := by
  let terminalData :=
    L.terminal.toLabelledOperationalTerminalData L.prime hclaw
  let D := terminalData.toOperationalTerminalData.toTerminalTetherData
  have hgenerated :
      FiniteMixedSideDistinctCenterGeneratedPropagationData T D hclaw := by
    simpa [terminalData, D] using L.propagation hclaw
  exact D.paperLemma14_of_distinctCenterConsequences hclaw
    hgenerated.toTraceData.toDistinctCenterConsequences

end InitializationFiniteMixedSideExecutableLemma14Data

/-- The literal adjacent link recorded when one incoming search stops on its
terminal component. This is local path-coordinate data, not the derived
same-colour two-step adjacency used by Lemma 14. -/
structure FiniteMixedSideCanonicalTerminalLink
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
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

/-- Literal positive stopping branch: the target is the introduced vertex of a
single-vertex deformation of the exact finite manuscript final hole. -/
structure FiniteMixedSidePositiveTerminalStop
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node) where
  positive :
    0 <
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount
  cloneIndex : Fin
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.card
  target_clone :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.SingleVertexDeformation
        (target : V) cloneIndex

/-- The two literal stopping branches of an incoming finite search. -/
inductive FiniteMixedSideIncomingTerminalHistory
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) : Type (u + 1) where
  | empty
      (blockCount_zero :
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount = 0)
      (link : FiniteMixedSideCanonicalTerminalLink
        T source target incoming)
  | positive
      (stop : FiniteMixedSidePositiveTerminalStop T source target)
      (link : FiniteMixedSideCanonicalTerminalLink
        T source target incoming)

namespace FiniteMixedSideIncomingTerminalHistory

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Forget the empty/positive branch while retaining its literal adjacent link. -/
def link
    (H : FiniteMixedSideIncomingTerminalHistory
      T source target incoming) :
    FiniteMixedSideCanonicalTerminalLink T source target incoming :=
  match H with
  | .empty _ L => L
  | .positive _ L => L

/-- A positive block count selects the positive constructor and yields its raw
final-hole clone. -/
theorem positive_target_clone
    (H : FiniteMixedSideIncomingTerminalHistory
      T source target incoming)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    ∃ i : Fin
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).manuscriptFinalHole.card,
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole.SingleVertexDeformation
          (target : V) i := by
  cases H with
  | empty hzero L => omega
  | positive S L => exact ⟨S.cloneIndex, S.target_clone⟩

/-- Convert the literal branch history to the raw canonical terminal stop used
by the established terminal analysis. -/
def toCanonicalTerminalStop
    (H : FiniteMixedSideIncomingTerminalHistory
      T source target incoming) :
    FiniteMixedSideIncomingCanonicalTerminalStop
      T source target incoming where
  positive_target_clone := H.positive_target_clone
  linkIndex := H.link.linkIndex
  link_center_eq := H.link.link_center_eq
  link_toward_target := H.link.link_toward_target

end FiniteMixedSideIncomingTerminalHistory

/-- Literal terminal histories for every initialized incoming obstruction arc. -/
structure InitializationFiniteMixedSideTerminalHistory
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  alternation : FiniteMixedSideTerminalStepAlternationData T
  stop : ∀ {source target : I.Node}
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingTerminalHistory T source target incoming

namespace InitializationFiniteMixedSideTerminalHistory

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Convert all raw stopping branches to the terminal event whose target
commutation, degree-three property, and two-step flank adjacency are derived. -/
def toStepTerminalEvent
    (H : InitializationFiniteMixedSideTerminalHistory T) :
    InitializationFiniteMixedSideStepTerminalEvent T where
  alternation := H.alternation
  stop := fun incoming => (H.stop incoming).toCanonicalTerminalStop

end InitializationFiniteMixedSideTerminalHistory

namespace InitializationPrimeVertexData

/-- Definition 20 defines the initializer set inside the fixed prime carrier. -/
def of_W_subset_Cprime
    (I : ObstructionSearchInitialization families Cprime)
    (hW : I.W ⊆ Cprime) :
    I.InitializationPrimeVertexData where
  node_mem_prime := fun j => hW j.property

end InitializationPrimeVertexData

/-- Complete finite initialized search history used by manuscript Lemma 14.

The propagation field does not contain an endpoint alternative or a terminal
claw. Its witnesses carry the indexed
`FiniteMixedSideDistinctPropagationTrace.IsGenerated` proof, so they are
assembled only from the finite zero-hop and actual-block `snoc` constructors. -/
structure InitializationFiniteMixedSideLemma14History
    (I : ObstructionSearchInitialization families Cprime) : Type (u + 1) where
  core : I.InitializationFiniteMixedSideTerminalCoreData
  W_subset_Cprime : I.W ⊆ Cprime
  terminal : InitializationFiniteMixedSideTerminalHistory core
  propagation : ∀ hclaw : G.IsClawFree,
    let prime := InitializationPrimeVertexData.of_W_subset_Cprime
      I W_subset_Cprime
    let terminalData :=
      terminal.toStepTerminalEvent.toLabelledOperationalTerminalData
        prime hclaw
    let D := terminalData.toOperationalTerminalData.toTerminalTetherData
    FiniteMixedSideDistinctCenterGeneratedPropagationData core D hclaw

namespace InitializationFiniteMixedSideLemma14History

/-- The literal inclusion `W ⊆ Cprime` supplies the prime-vertex interface used
by finite Lemma 11(a). -/
def toPrimeVertexData
    (H : I.InitializationFiniteMixedSideLemma14History) :
    I.InitializationPrimeVertexData :=
  InitializationPrimeVertexData.of_W_subset_Cprime I H.W_subset_Cprime

/-- Construct the modular executable bridge from the literal history. -/
def toExecutableLemma14Data
    (H : I.InitializationFiniteMixedSideLemma14History) :
    InitializationFiniteMixedSideExecutableLemma14Data H.core where
  prime := H.toPrimeVertexData
  terminal := H.terminal.toStepTerminalEvent
  propagation := by
    intro hclaw
    simpa [toPrimeVertexData] using H.propagation hclaw

/-- Exact four-part manuscript Lemma 14 from the initialized finite search
history and claw-freeness. -/
theorem paperLemma14
    (H : I.InitializationFiniteMixedSideLemma14History)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I :=
  H.toExecutableLemma14Data.paperLemma14_of_executableData hclaw

end InitializationFiniteMixedSideLemma14History

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
