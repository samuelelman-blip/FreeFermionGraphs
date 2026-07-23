import FreeFermionGraphs.Lemma11Complete
import FreeFermionGraphs.ObstructionSearchTerminalPredecessorOccurrence

/-!
# Lemma 14(iv): deriving predecessor anticommutation

The remaining first-block predecessor occurrence still stored anticommutation
with the active path as an independent field.  This is forced by the other
local facts.

Indeed, the predecessor belongs to a Definition 20 dependent set and has final
hole degree three.  If it commuted with the active path, Lemma 11(b) would give
final degree four.  Therefore anticommutation follows from the complete
formalized Lemma 11 theorem and need not remain part of the terminal
propagation boundary.
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

/-- A first-block predecessor occurrence without a separately supplied
anticommutation certificate. -/
structure FirstBlockPredecessorDegreeOccurrence
    (T : I.InitializationTerminalCoreData)
    (source : I.Node)
    (previous : V) where
  blockIndex : Fin (T.executionTrace.execution source).blockCount
  block_is_first :
    ∃ F :
        ((T.executionTrace.execution source).concreteBlock
          blockIndex).FullDefinition19Lemma11AData,
      (T.executionTrace.execution source).blockContext blockIndex =
        ConcretePathDeformation.Lemma11AHistoryContext.first F
  step : Nat
  mem_dependent :
    previous ∈
      ((T.executionTrace.execution source).concreteBlock
        blockIndex).dependentAt step
  finalDegree_three :
    ((T.executionTrace.execution source).concreteBlock
      blockIndex).finalHole.externalDegree previous = 3

namespace FirstBlockPredecessorDegreeOccurrence

variable {T : I.InitializationTerminalCoreData}
  {source : I.Node} {previous : V}

/-- Dependent-set membership supplies prime-set membership. -/
theorem mem_prime
    (W : FirstBlockPredecessorDegreeOccurrence T source previous) :
    previous ∈ Cprime :=
  ConcretePathDeformation.mem_prime_of_mem_dependentAt
    ((T.executionTrace.execution source).concreteBlock W.blockIndex)
    W.mem_dependent

/-- Final degree three rules out the commuting branch of Lemma 11(b), which
would force final degree four. -/
theorem anticommutes
    (W : FirstBlockPredecessorDegreeOccurrence T source previous)
    (hclaw : G.IsClawFree) :
    ((T.executionTrace.execution source).concreteBlock
      W.blockIndex).path.AnticommutesWith previous := by
  by_contra hcomm
  let D := (T.executionTrace.execution source).concreteBlock W.blockIndex
  let H := (T.executionTrace.execution source).blockContext W.blockIndex
  have hfour :=
    ((D.lemma11 H hclaw W.mem_prime).2 W.step W.mem_dependent hcomm).1
  have hfour' : D.finalHole.externalDegree previous = 4 := by
    simpa [ConcretePathDeformation.finalDegree] using hfour
  have hthree : D.finalHole.externalDegree previous = 3 := by
    simpa [D] using W.finalDegree_three
  omega

/-- Recover the prior predecessor occurrence with anticommutation derived from
Lemma 11(b). -/
def toPredecessorOccurrence
    (W : FirstBlockPredecessorDegreeOccurrence T source previous)
    (hclaw : G.IsClawFree) :
    FirstBlockPredecessorOccurrence T source previous where
  blockIndex := W.blockIndex
  block_is_first := W.block_is_first
  step := W.step
  mem_dependent := W.mem_dependent
  anticommutes := W.anticommutes hclaw
  finalDegree_three := W.finalDegree_three

end FirstBlockPredecessorDegreeOccurrence

/-- Remaining distinct-clone propagation data after removing predecessor
anticommutation from the certificate boundary. -/
structure DistinctClonePropagationFromDegreeOccurrence
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  previous : V
  predecessorOccurrence :
    Nonempty (FirstBlockPredecessorDegreeOccurrence T source previous)
  center : V
  propagatedNeighbor : V
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  propagatedNeighbor_ne_previousNeighbor :
    ∀ q : Fin T.executionTrace.originalHole.card,
      G.Adj previous (T.executionTrace.originalHole.vertex q) →
        propagatedNeighbor ≠ T.executionTrace.originalHole.vertex q
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range T.executionTrace.originalHole.vertex
  cloneGeometry :
    DistinctCloneGeometryWithoutPreviousPair T hclaw source target incoming
      center previous propagatedNeighbor

namespace DistinctClonePropagationFromDegreeOccurrence

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Choose a concrete predecessor occurrence only when converting to the prior
interface; its anticommutation field is proved from Lemma 11(b). -/
noncomputable def toPropagationFromOccurrence
    (X : DistinctClonePropagationFromDegreeOccurrence
      T hclaw source target incoming) :
    DistinctClonePropagationFromOccurrence T hclaw source target incoming := by
  let W : FirstBlockPredecessorDegreeOccurrence T source X.previous :=
    Classical.choice X.predecessorOccurrence
  exact
    { previous := X.previous
      predecessorOccurrence := ⟨W.toPredecessorOccurrence hclaw⟩
      center := X.center
      propagatedNeighbor := X.propagatedNeighbor
      adj_previous := X.adj_previous
      adj_propagatedNeighbor := X.adj_propagatedNeighbor
      previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
      propagatedNeighbor_ne_previousNeighbor :=
        X.propagatedNeighbor_ne_previousNeighbor
      propagatedNeighbor_mem_originalHole :=
        X.propagatedNeighbor_mem_originalHole
      cloneGeometry := X.cloneGeometry }

/-- The reduced occurrence package still yields the final distinct-clone
contradiction. -/
theorem false_of_clawFree
    (X : DistinctClonePropagationFromDegreeOccurrence
      T hclaw source target incoming) : False :=
  X.toPropagationFromOccurrence.false_of_clawFree

end DistinctClonePropagationFromDegreeOccurrence

/-- Same-clone geometry or distinct-clone propagation whose predecessor
anticommutation is derived from its dependent membership and degree. -/
inductive TwoIncomingInteriorGeometryFromDegreeOccurrences
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source source' target : I.Node)
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometryFromDegreeOccurrences
        T hclaw source source' target incoming incoming'
  | distinctClone :
      (Nonempty
          (DistinctClonePropagationFromDegreeOccurrence
            T hclaw source target incoming) ∨
        Nonempty
          (DistinctClonePropagationFromDegreeOccurrence
            T hclaw source' target incoming')) →
      TwoIncomingInteriorGeometryFromDegreeOccurrences
        T hclaw source source' target incoming incoming'

/-- Pairwise terminal analysis with predecessor anticommutation removed from
the primitive distinct-clone data. -/
structure TwoIncomingTerminalPredecessorDegreeAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target),
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        TwoIncomingInteriorGeometryFromDegreeOccurrences
          T hclaw source source' target incoming incoming'

namespace TwoIncomingTerminalPredecessorDegreeAnalysis

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}

/-- Convert the degree-only predecessor analysis to the previous existential
occurrence interface. -/
noncomputable def toTerminalOccurrenceAnalysis
    (A : TwoIncomingTerminalPredecessorDegreeAnalysis T hclaw) :
    TwoIncomingTerminalOccurrenceAnalysis T hclaw where
  interiorGeometry := by
    intro source source' target hne incoming incoming' hsource hsource'
    rcases A.interiorGeometry hne incoming incoming' hsource hsource' with
      hsame | hdistinct
    · exact TwoIncomingInteriorGeometryFromOccurrences.sameClone hsame
    · apply TwoIncomingInteriorGeometryFromOccurrences.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationFromOccurrence⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationFromOccurrence⟩

end TwoIncomingTerminalPredecessorDegreeAnalysis

namespace InitializationTerminalCoreData

/-- Lemma 14 from a terminal analysis in which predecessor anticommutation is a
consequence of Lemma 11(b), not an independent propagation certificate. -/
theorem lemma14_of_terminalPredecessorDegreeAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (A : TwoIncomingTerminalPredecessorDegreeAnalysis T hclaw) :
    (∀ source : I.Node,
      (I.output source).run = none ∨
        ∃ F : FullDefinition19Deformation
            (families (I.pairing source)) Cprime,
          (I.output source).run = some F) ∧
    I.graph.IsBipartiteByPairing I.pairing ∧
    (∀ ⦃source source' : I.Node⦄,
      source ≠ source' →
      I.pairing source = I.pairing source' →
        Disjoint (I.output source).paths
          (I.output source').paths) ∧
    ((∀ target : I.Node, I.graph.AtMostTwoIncoming target) ∧
      ∀ ⦃source source' target : I.Node⦄,
        source ≠ source' →
        I.graph.Arc source target →
        I.graph.Arc source' target →
          ((I.dependentSet source = {(target : V)} ∧
              I.dependentSet source' ≠ {(target : V)}) ∨
            (I.dependentSet source ≠ {(target : V)} ∧
              I.dependentSet source' = {(target : V)}))) := by
  exact T.lemma14_of_terminalOccurrenceAnalysis hclaw
    A.toTerminalOccurrenceAnalysis

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
