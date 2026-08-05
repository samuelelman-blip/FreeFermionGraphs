import FreeFermionGraphs.ObstructionSearchFiniteMixedExecutablePaperLemma14

/-!
# Complete manuscript-level initialization history for Lemma 14

The initialized obstruction search is not merely a terminal certificate.  It is
the finite execution history appearing in Definitions 19 and 20, together with
its literal stopping branches.

This module packages that manuscript setup in one object.  The four terminal
facts used by Lemma 14 are derived from the history:

* global terminal-path parity is derived from local step alternation;
* positive terminal degree three is derived from the raw final-hole clone and
  then from target commutation;
* clone-to-flank adjacency is derived from the canonical adjacent link; and
* unequal-centre propagation is required to carry the existing inductive
  `IsGenerated` history built only by `start` and `snoc`.

The paper-facing theorem below therefore has one manuscript setup argument and
claw-freeness, rather than a separate post-hoc Lemma 14 certificate.
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

/-- The literal adjacent link recorded when one incoming search stops on its
terminal component.  This is local path-coordinate data, not the derived
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

/-- The two literal stopping branches of an incoming finite search.

The empty branch records that no Definition 19 block was appended.  The
positive branch records the final single-vertex deformation.  Both branches
carry the adjacent terminal link emitted by the stopping rule. -/
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

/-- A positive block count selects the positive constructor and hence yields
its raw final-hole clone. -/
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

/-- Literal terminal histories for every initialized incoming obstruction arc.
Local colour alternation is the path-component data emitted by the search;
parity labels are derived from it. -/
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

/-- The complete finite initialization history appearing in the manuscript
setup of Lemma 14.

`propagation` is not an arbitrary trace.  Its witnesses carry the inductive
`FiniteMixedSideDistinctPropagationTrace.IsGenerated` derivation, so every
bounded trace is assembled only by the literal zero-hop and `snoc` execution
constructors. -/
structure InitializationFiniteMixedSideLemma14History
    (I : ObstructionSearchInitialization families Cprime) : Type (u + 1) where
  core : I.InitializationFiniteMixedSideTerminalCoreData
  W_subset_Cprime : I.W ⊆ Cprime
  terminal : InitializationFiniteMixedSideTerminalHistory core
  propagation : ∀ hclaw : G.IsClawFree,
    let prime := I.InitializationPrimeVertexData.of_W_subset_Cprime
      W_subset_Cprime
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
  I.InitializationPrimeVertexData.of_W_subset_Cprime H.W_subset_Cprime

/-- The integrated history constructs the established executable bridge.  All
terminal conclusions are computed from the local alternation and stopping
constructors; propagation witnesses retain their inductive generation proof. -/
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
