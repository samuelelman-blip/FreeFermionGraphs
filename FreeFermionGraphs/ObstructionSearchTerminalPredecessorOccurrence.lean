import FreeFermionGraphs.ObstructionSearchTerminalArcData

/-!
# Lemma 14(iv): existential first-block predecessor occurrence

The manuscript's long distinct-clone propagation identifies a predecessor
`j_{p-2}` which occurs in a dependent set of the first Definition 19 block,
anticommutes with that block's active path, and has final degree three.  The
particular block and step indices are witnesses to this statement, not
canonical data of the terminal geometry.

This module packages those indices existentially.  The remaining terminal
interface exposes the predecessor vertex and the existence of a suitable
first-block occurrence, while a noncomputable conversion chooses indices only
when constructing the previously formalized execution-level contradiction.
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

/-- A concrete occurrence of the propagated predecessor in a dependent set of
a first Definition 19 block, together with the two local conclusions used by
Lemma 11(a). -/
structure FirstBlockPredecessorOccurrence
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
  anticommutes :
    ((T.executionTrace.execution source).concreteBlock
      blockIndex).path.AnticommutesWith previous
  finalDegree_three :
    ((T.executionTrace.execution source).concreteBlock
      blockIndex).finalHole.externalDegree previous = 3

/-- Remaining distinct-clone propagation data after hiding the noncanonical
block and step indices of the predecessor occurrence. -/
structure DistinctClonePropagationFromOccurrence
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  previous : V
  predecessorOccurrence :
    Nonempty (FirstBlockPredecessorOccurrence T source previous)
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

namespace DistinctClonePropagationFromOccurrence

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Choose one concrete first-block predecessor occurrence only at the point
where the execution-level propagation package is assembled. -/
noncomputable def toPropagationFromArc
    (X : DistinctClonePropagationFromOccurrence
      T hclaw source target incoming) :
    DistinctClonePropagationFromArc T hclaw source target incoming := by
  let W : FirstBlockPredecessorOccurrence T source X.previous :=
    Classical.choice X.predecessorOccurrence
  exact
    { dependentBlockIndex := W.blockIndex
      dependentBlock_is_first := W.block_is_first
      dependentStep := W.step
      previous := X.previous
      previous_mem_dependent := W.mem_dependent
      previous_anticommutes := W.anticommutes
      previous_finalDegree_three := W.finalDegree_three
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

/-- The occurrence-level package still yields the final distinct-clone claw. -/
theorem false_of_clawFree
    (X : DistinctClonePropagationFromOccurrence
      T hclaw source target incoming) : False :=
  X.toPropagationFromArc.false_of_clawFree

end DistinctClonePropagationFromOccurrence

/-- Same-clone geometry or distinct-clone propagation with the predecessor's
first-block occurrence represented existentially. -/
inductive TwoIncomingInteriorGeometryFromOccurrences
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source source' target : I.Node)
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometryFromOccurrences
        T hclaw source source' target incoming incoming'
  | distinctClone :
      (Nonempty
          (DistinctClonePropagationFromOccurrence
            T hclaw source target incoming) ∨
        Nonempty
          (DistinctClonePropagationFromOccurrence
            T hclaw source' target incoming')) →
      TwoIncomingInteriorGeometryFromOccurrences
        T hclaw source source' target incoming incoming'

/-- Pairwise terminal analysis without selected block or step indices for the
first-block predecessor occurrence. -/
structure TwoIncomingTerminalOccurrenceAnalysis
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
        TwoIncomingInteriorGeometryFromOccurrences
          T hclaw source source' target incoming incoming'

namespace TwoIncomingTerminalOccurrenceAnalysis

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}

/-- Convert the existential-occurrence analysis to the arc-parameterized
interface. -/
noncomputable def toTerminalArcAnalysis
    (A : TwoIncomingTerminalOccurrenceAnalysis T hclaw) :
    TwoIncomingTerminalArcAnalysis T hclaw where
  interiorGeometry := by
    intro source source' target hne incoming incoming' hsource hsource'
    rcases A.interiorGeometry hne incoming incoming' hsource hsource' with
      hsame | hdistinct
    · exact TwoIncomingInteriorGeometryFromArcs.sameClone hsame
    · apply TwoIncomingInteriorGeometryFromArcs.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationFromArc⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationFromArc⟩

end TwoIncomingTerminalOccurrenceAnalysis

namespace InitializationTerminalCoreData

/-- Lemma 14 from a terminal analysis that asserts only the existence of the
first-block predecessor occurrence required by the manuscript. -/
theorem lemma14_of_terminalOccurrenceAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (A : TwoIncomingTerminalOccurrenceAnalysis T hclaw) :
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
  exact T.lemma14_of_terminalArcAnalysis hclaw A.toTerminalArcAnalysis

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
