import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalArcData

/-!
# Existential finite predecessor occurrence

The manuscript's distinct-clone propagation identifies a predecessor that
occurs in a dependent set of a first finite Definition 19 block, anticommutes
with that block's active path, and has final degree three.  The particular
block and step indices witness this statement but are not canonical terminal
geometry.

This module packages those indices existentially.  A concrete occurrence is
chosen only when assembling the already proved finite arc-parameterized
contradiction.
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

/-- A concrete occurrence of the propagated predecessor in a dependent set
of a finite first block, together with the local facts used by Lemma 11(a). -/
structure FiniteMixedSideFirstBlockPredecessorOccurrence
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source : I.Node)
    (previous : V) where
  blockIndex : Fin
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).blockCount
  block_initial_eq_original :
    Set.range
        ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).block blockIndex).initialHole.vertex =
      Set.range
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  step : Nat
  mem_dependent :
    previous ∈
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block blockIndex).dependentAt step
  anticommutes :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block blockIndex).path.AnticommutesWith previous
  finalDegree_three :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block blockIndex).finalHole.externalDegree previous = 3

/-- Finite distinct-clone propagation after hiding the noncanonical block and
step indices of the predecessor occurrence. -/
structure FiniteMixedSideDistinctClonePropagationFromOccurrence
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  previous : V
  predecessorOccurrence :
    Nonempty
      (FiniteMixedSideFirstBlockPredecessorOccurrence T source previous)
  center : V
  propagatedNeighbor : V
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  propagatedNeighbor_ne_previousNeighbor :
    ∀ q : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      G.Adj previous
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q) →
        propagatedNeighbor ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  cloneGeometry :
    FiniteMixedSideDistinctCloneGeometryWithoutPreviousPair
      T target center previous propagatedNeighbor

namespace FiniteMixedSideDistinctClonePropagationFromOccurrence

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Choose one concrete first-block predecessor occurrence only while
assembling the finite arc-parameterized propagation package. -/
noncomputable def toPropagationFromArc
    (X : FiniteMixedSideDistinctClonePropagationFromOccurrence
      T source target incoming) :
    FiniteMixedSideDistinctClonePropagationFromArc
      T source target incoming := by
  let W : FiniteMixedSideFirstBlockPredecessorOccurrence
      T source X.previous :=
    Classical.choice X.predecessorOccurrence
  exact
    { dependentBlockIndex := W.blockIndex
      dependentBlock_initial_eq_original := W.block_initial_eq_original
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

/-- The occurrence-level finite package still yields the final claw
contradiction. -/
theorem false_of_clawFree
    (X : FiniteMixedSideDistinctClonePropagationFromOccurrence
      T source target incoming)
    (hclaw : G.IsClawFree) : False :=
  X.toPropagationFromArc.false_of_clawFree hclaw

end FiniteMixedSideDistinctClonePropagationFromOccurrence

/-- Same-clone geometry or finite distinct-clone propagation with the
predecessor's first-block occurrence represented existentially. -/
inductive FiniteMixedSideTwoIncomingInteriorGeometryFromOccurrences
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source source' target : I.Node)
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      FiniteMixedSideTwoIncomingInteriorGeometryFromOccurrences
        T source source' target incoming incoming'
  | distinctClone :
      (Nonempty
          (FiniteMixedSideDistinctClonePropagationFromOccurrence
            T source target incoming) ∨
        Nonempty
          (FiniteMixedSideDistinctClonePropagationFromOccurrence
            T source' target incoming')) →
      FiniteMixedSideTwoIncomingInteriorGeometryFromOccurrences
        T source source' target incoming incoming'

/-- Pairwise finite terminal analysis without selected block or step indices
for the first-block predecessor occurrence. -/
structure FiniteMixedSideTwoIncomingTerminalOccurrenceAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target),
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        FiniteMixedSideTwoIncomingInteriorGeometryFromOccurrences
          T source source' target incoming incoming'

namespace FiniteMixedSideTwoIncomingTerminalOccurrenceAnalysis

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Convert the existential-occurrence analysis to the finite
arc-parameterized interface. -/
noncomputable def toTerminalArcAnalysis
    (A : FiniteMixedSideTwoIncomingTerminalOccurrenceAnalysis T) :
    FiniteMixedSideTwoIncomingTerminalArcAnalysis T where
  interiorGeometry := by
    intro source source' target hne incoming incoming' hsource hsource'
    rcases A.interiorGeometry
        hne incoming incoming' hsource hsource' with hsame | hdistinct
    · exact FiniteMixedSideTwoIncomingInteriorGeometryFromArcs.sameClone hsame
    · apply FiniteMixedSideTwoIncomingInteriorGeometryFromArcs.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationFromArc⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationFromArc⟩

end FiniteMixedSideTwoIncomingTerminalOccurrenceAnalysis

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Lemma 14 from a finite terminal analysis asserting only the existence of
the first-block predecessor occurrence required by the manuscript. -/
theorem lemma14_of_terminalOccurrenceAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalOccurrenceAnalysis T)
    (hclaw : G.IsClawFree) :
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
              I.dependentSet source' = {(target : V)}))) :=
  T.lemma14_of_terminalArcAnalysis A.toTerminalArcAnalysis hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
