import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalDistinctClone
import FreeFermionGraphs.ObstructionSearchTerminalDistinctCloneNeighbors

/-!
# Deriving finite alternative-clone neighbours

The two original-hole neighbours of the alternative clone in the final
Lemma 14(iv) contradiction are supplied by the indexed cycle itself.  They
are not independent output of the obstruction-search loop.

This module removes the chosen neighbour indices and cyclic-adjacency
certificates from the finite mixed-side propagation boundary.  The remaining
propagation statement says only that the propagated original-hole neighbour
is different from every original-hole neighbour of the alternative clone.
The canonical cycle-neighbour pair is selected afterwards.
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

/-- Finite distinct-clone propagation without a preselected pair of
original-hole neighbours for the alternative clone. -/
structure FiniteMixedSideDistinctClonePropagationWithoutChosenNeighbors
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node) where
  incoming : I.graph.Arc source target
  dependentBlockIndex : Fin
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).blockCount
  dependentBlock_initial_eq_original :
    Set.range
        ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).block dependentBlockIndex).initialHole.vertex =
      Set.range
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  dependentStep : Nat
  previous : V
  previous_mem_dependent :
    previous ∈
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block dependentBlockIndex).dependentAt dependentStep
  previous_mem_prime : previous ∈ Cprime
  previous_anticommutes :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block dependentBlockIndex).path.AnticommutesWith previous
  previous_finalDegree_three :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block dependentBlockIndex).finalHole.externalDegree previous = 3
  center : V
  propagatedNeighbor : V
  cloneIndex : Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  target_clone :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
      (target : V) cloneIndex
  previousNeighbor0Index : Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  previousNeighbor1Index : Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  previousNeighbor0_ne_previousNeighbor1 :
    previousNeighbor0Index ≠ previousNeighbor1Index
  adj_previousNeighbor0 :
    G.Adj previous
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor0Index)
  adj_previousNeighbor1 :
    G.Adj previous
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor1Index)
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  adj_cloneCenter :
    G.Adj center
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex)
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  previous_ne_cloneCenter :
    previous ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex
  propagatedNeighbor_ne_cloneCenter :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex
  propagatedNeighbor_ne_previousNeighbor0 :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor0Index
  propagatedNeighbor_ne_previousNeighbor1 :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor1Index
  cloneCenter_ne_previousNeighbor0 :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor0Index
  cloneCenter_ne_previousNeighbor1 :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        cloneIndex ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor1Index
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  propagatedNeighbor_ne_cycleNeighbor :
    ∀ q : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      G.Adj
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            cloneIndex)
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            q) →
        propagatedNeighbor ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            q

namespace FiniteMixedSideDistinctClonePropagationWithoutChosenNeighbors

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}

/-- Select the alternative clone's two cycle neighbours and recover the full
finite propagation object. -/
noncomputable def toPropagationData
    (X : FiniteMixedSideDistinctClonePropagationWithoutChosenNeighbors
      T source target) :
    FiniteMixedSideDistinctClonePropagationData T source target := by
  let C :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole
  let B := C.cycleNeighborPair X.cloneIndex
  exact
    { incoming := X.incoming
      dependentBlockIndex := X.dependentBlockIndex
      dependentBlock_initial_eq_original :=
        X.dependentBlock_initial_eq_original
      dependentStep := X.dependentStep
      previous := X.previous
      previous_mem_dependent := X.previous_mem_dependent
      previous_mem_prime := X.previous_mem_prime
      previous_anticommutes := X.previous_anticommutes
      previous_finalDegree_three := X.previous_finalDegree_three
      center := X.center
      propagatedNeighbor := X.propagatedNeighbor
      cloneIndex := X.cloneIndex
      target_clone := X.target_clone
      previousNeighbor0Index := X.previousNeighbor0Index
      previousNeighbor1Index := X.previousNeighbor1Index
      previousNeighbor0_ne_previousNeighbor1 :=
        X.previousNeighbor0_ne_previousNeighbor1
      adj_previousNeighbor0 := X.adj_previousNeighbor0
      adj_previousNeighbor1 := X.adj_previousNeighbor1
      cloneNeighbor0Index := B.left
      cloneNeighbor1Index := B.right
      cloneNeighbor0_ne_cloneNeighbor1 := B.left_ne_right
      cloneNeighbor0_cyclic := (C.adj_iff X.cloneIndex B.left).1 B.adj_left
      cloneNeighbor1_cyclic := (C.adj_iff X.cloneIndex B.right).1 B.adj_right
      adj_previous := X.adj_previous
      adj_propagatedNeighbor := X.adj_propagatedNeighbor
      adj_cloneCenter := X.adj_cloneCenter
      previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
      previous_ne_cloneCenter := X.previous_ne_cloneCenter
      propagatedNeighbor_ne_cloneCenter := X.propagatedNeighbor_ne_cloneCenter
      propagatedNeighbor_ne_previousNeighbor0 :=
        X.propagatedNeighbor_ne_previousNeighbor0
      propagatedNeighbor_ne_previousNeighbor1 :=
        X.propagatedNeighbor_ne_previousNeighbor1
      cloneCenter_ne_previousNeighbor0 := X.cloneCenter_ne_previousNeighbor0
      cloneCenter_ne_previousNeighbor1 := X.cloneCenter_ne_previousNeighbor1
      propagatedNeighbor_mem_originalHole :=
        X.propagatedNeighbor_mem_originalHole
      propagatedNeighbor_ne_cloneNeighbor0 :=
        X.propagatedNeighbor_ne_cycleNeighbor B.left B.adj_left
      propagatedNeighbor_ne_cloneNeighbor1 :=
        X.propagatedNeighbor_ne_cycleNeighbor B.right B.adj_right }

/-- The reduced finite propagation package still yields the final claw
contradiction. -/
theorem false_of_clawFree
    (X : FiniteMixedSideDistinctClonePropagationWithoutChosenNeighbors
      T source target)
    (hclaw : G.IsClawFree) : False :=
  X.toPropagationData.false_of_clawFree hclaw

end FiniteMixedSideDistinctClonePropagationWithoutChosenNeighbors

/-- Same-clone geometry or finite distinct-clone propagation without chosen
alternative-clone neighbours. -/
inductive FiniteMixedSideTwoIncomingInteriorGeometryWithoutChosenNeighbors
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      FiniteMixedSideTwoIncomingInteriorGeometryWithoutChosenNeighbors
        T source source' target
  | distinctClone :
      (Nonempty
          (FiniteMixedSideDistinctClonePropagationWithoutChosenNeighbors
            T source target) ∨
        Nonempty
          (FiniteMixedSideDistinctClonePropagationWithoutChosenNeighbors
            T source' target)) →
      FiniteMixedSideTwoIncomingInteriorGeometryWithoutChosenNeighbors
        T source source' target

/-- Pairwise finite terminal analysis with the alternative clone's cycle
neighbours derived rather than supplied. -/
structure FiniteMixedSideTwoIncomingTerminalNeighborAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        FiniteMixedSideTwoIncomingInteriorGeometryWithoutChosenNeighbors
          T source source' target

namespace FiniteMixedSideTwoIncomingTerminalNeighborAnalysis

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Convert the reduced finite terminal analysis to the complete finite claw
analysis. -/
noncomputable def toTerminalClawAnalysis
    (A : FiniteMixedSideTwoIncomingTerminalNeighborAnalysis T) :
    FiniteMixedSideTwoIncomingTerminalClawAnalysis T where
  interiorGeometry := by
    intro source source' target hne incoming incoming' hsource hsource'
    rcases A.interiorGeometry
        hne incoming incoming' hsource hsource' with hsame | hdistinct
    · exact FiniteMixedSideTwoIncomingInteriorGeometry.sameClone hsame
    · apply FiniteMixedSideTwoIncomingInteriorGeometry.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationData⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationData⟩

end FiniteMixedSideTwoIncomingTerminalNeighborAnalysis

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Lemma 14 from the finite terminal core and the reduced pairwise analysis
without chosen alternative-clone neighbours. -/
theorem lemma14_of_terminalNeighborAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalNeighborAnalysis T)
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
  T.lemma14_of_terminalClawAnalysis A.toTerminalClawAnalysis hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
