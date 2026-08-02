import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalCloneFromStopping
import FreeFermionGraphs.ObstructionSearchTerminalPreviousNeighbors

/-!
# Deriving the finite predecessor neighbours

In the final distinct-clone propagation, the predecessor is a dependent
vertex of a finite first block with final degree three.  Its degree on the
initialized original hole is therefore exactly two.  The two original-hole
neighbours of the predecessor are consequently derived data, not independent
output of the propagation loop.

This module removes their chosen indices, distinctness, and adjacency
certificates from the finite propagation boundary.  The long propagation now
records only uniform inequalities against every original-hole neighbour of
the predecessor.
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

/-- Clone-centre geometry after removing a chosen predecessor-neighbour pair. -/
structure FiniteMixedSideDistinctCloneGeometryWithoutPreviousPair
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (target : I.Node)
    (center previous propagatedNeighbor : V) : Prop where
  adj_cloneCenter :
    ∀ cloneIndex : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        G.Adj center
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            cloneIndex)
  previous_ne_cloneCenter :
    ∀ cloneIndex : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        previous ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            cloneIndex
  propagatedNeighbor_ne_cloneCenter :
    ∀ cloneIndex : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        propagatedNeighbor ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            cloneIndex
  cloneCenter_ne_previousNeighbor :
    ∀ (cloneIndex q : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card),
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
      G.Adj previous
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q) →
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            cloneIndex ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q
  propagatedNeighbor_ne_cycleNeighbor :
    ∀ (cloneIndex q : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card),
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
      G.Adj
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            cloneIndex)
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q) →
        propagatedNeighbor ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q

/-- Finite distinct-clone propagation without a chosen pair of original-hole
neighbours of the predecessor. -/
structure FiniteMixedSideDistinctClonePropagationWithoutPreviousPair
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

namespace FiniteMixedSideDistinctClonePropagationWithoutPreviousPair

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}

/-- The predecessor has degree two on the initialized original hole. -/
theorem previous_originalDegree_two
    (X : FiniteMixedSideDistinctClonePropagationWithoutPreviousPair
      T source target)
    (hclaw : G.IsClawFree) :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.externalDegree
      X.previous = 2 :=
  T.execution.toInitializationFiniteMixedSideOSExecutionData.originalDegree_two_of_firstBlock_dependent
    source X.dependentBlockIndex X.dependentBlock_initial_eq_original
    hclaw X.previous_mem_dependent X.previous_mem_prime
    X.previous_anticommutes X.previous_finalDegree_three

/-- Select the predecessor's two original-hole neighbours from its derived
degree and recover the stopping-relative finite propagation package. -/
noncomputable def toPropagationFromStopping
    (X : FiniteMixedSideDistinctClonePropagationWithoutPreviousPair
      T source target)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideDistinctClonePropagationFromStopping T source target := by
  let C :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole
  let B := C.externalNeighborPair X.previous
    (X.previous_originalDegree_two hclaw)
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
      previousNeighbor0Index := B.left
      previousNeighbor1Index := B.right
      previousNeighbor0_ne_previousNeighbor1 := B.left_ne_right
      adj_previousNeighbor0 := B.adj_left
      adj_previousNeighbor1 := B.adj_right
      adj_previous := X.adj_previous
      adj_propagatedNeighbor := X.adj_propagatedNeighbor
      previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
      propagatedNeighbor_ne_previousNeighbor0 :=
        X.propagatedNeighbor_ne_previousNeighbor B.left B.adj_left
      propagatedNeighbor_ne_previousNeighbor1 :=
        X.propagatedNeighbor_ne_previousNeighbor B.right B.adj_right
      propagatedNeighbor_mem_originalHole :=
        X.propagatedNeighbor_mem_originalHole
      cloneGeometry :=
        { adj_cloneCenter := X.cloneGeometry.adj_cloneCenter
          previous_ne_cloneCenter := X.cloneGeometry.previous_ne_cloneCenter
          propagatedNeighbor_ne_cloneCenter :=
            X.cloneGeometry.propagatedNeighbor_ne_cloneCenter
          cloneCenter_ne_previousNeighbor0 := by
            intro cloneIndex hclone
            exact X.cloneGeometry.cloneCenter_ne_previousNeighbor
              cloneIndex B.left hclone B.adj_left
          cloneCenter_ne_previousNeighbor1 := by
            intro cloneIndex hclone
            exact X.cloneGeometry.cloneCenter_ne_previousNeighbor
              cloneIndex B.right hclone B.adj_right
          propagatedNeighbor_ne_cycleNeighbor :=
            X.cloneGeometry.propagatedNeighbor_ne_cycleNeighbor } }

/-- The predecessor-pair-free finite package still yields the final claw
contradiction. -/
theorem false_of_clawFree
    (X : FiniteMixedSideDistinctClonePropagationWithoutPreviousPair
      T source target)
    (hclaw : G.IsClawFree) : False :=
  (X.toPropagationFromStopping hclaw).false_of_clawFree hclaw

end FiniteMixedSideDistinctClonePropagationWithoutPreviousPair

/-- Same-clone geometry or finite distinct-clone propagation without a chosen
predecessor-neighbour pair. -/
inductive FiniteMixedSideTwoIncomingInteriorGeometryWithoutPreviousPair
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      FiniteMixedSideTwoIncomingInteriorGeometryWithoutPreviousPair
        T source source' target
  | distinctClone :
      (Nonempty
          (FiniteMixedSideDistinctClonePropagationWithoutPreviousPair
            T source target) ∨
        Nonempty
          (FiniteMixedSideDistinctClonePropagationWithoutPreviousPair
            T source' target)) →
      FiniteMixedSideTwoIncomingInteriorGeometryWithoutPreviousPair
        T source source' target

/-- Pairwise finite terminal analysis after eliminating the predecessor's
chosen original-hole-neighbour pair. -/
structure FiniteMixedSideTwoIncomingTerminalPreviousNeighborAnalysis
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
        FiniteMixedSideTwoIncomingInteriorGeometryWithoutPreviousPair
          T source source' target

namespace FiniteMixedSideTwoIncomingTerminalPreviousNeighborAnalysis

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Convert the predecessor-pair-free finite analysis to the stopping-relative
finite interface. -/
noncomputable def toTerminalStoppingAnalysis
    (A : FiniteMixedSideTwoIncomingTerminalPreviousNeighborAnalysis T)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideTwoIncomingTerminalStoppingAnalysis T where
  interiorGeometry := by
    intro source source' target hne incoming incoming' hsource hsource'
    rcases A.interiorGeometry
        hne incoming incoming' hsource hsource' with hsame | hdistinct
    · exact FiniteMixedSideTwoIncomingInteriorGeometryFromStopping.sameClone
        hsame
    · apply
        FiniteMixedSideTwoIncomingInteriorGeometryFromStopping.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationFromStopping hclaw⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationFromStopping hclaw⟩

end FiniteMixedSideTwoIncomingTerminalPreviousNeighborAnalysis

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Lemma 14 from a finite terminal analysis in which neither the target
clone centre and its cycle neighbours nor the predecessor's original-hole
neighbours are selected as primitive propagation data. -/
theorem lemma14_of_terminalPreviousNeighborAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalPreviousNeighborAnalysis T)
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
  T.lemma14_of_terminalStoppingAnalysis
    (A.toTerminalStoppingAnalysis hclaw) hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
