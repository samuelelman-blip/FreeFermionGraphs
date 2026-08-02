import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalPreviousNeighbors
import FreeFermionGraphs.ObstructionSearchTerminalArcData

/-!
# Deriving finite prime and incoming-arc data

The finite distinct-clone propagation still repeated two facts determined by
its context.  Membership in a concrete Definition 20 dependent set already
implies membership in the prime carrier, and the incoming obstruction arc is
an argument of the pairwise terminal analysis.

This module derives prime membership and parameterizes the remaining finite
propagation data by the actual incoming arc.  The long propagation is left
responsible only for the geometric information not already forced by the
literal finite execution.
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

/-- Finite distinct-clone propagation parameterized by the actual incoming
obstruction arc.  It stores neither that arc nor separate prime membership of
the predecessor. -/
structure FiniteMixedSideDistinctClonePropagationFromArc
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
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

namespace FiniteMixedSideDistinctClonePropagationFromArc

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Recover the preceding finite propagation interface, deriving prime
membership from the concrete dependent-set occurrence and reusing the incoming
arc parameter. -/
def toPropagationWithoutPreviousPair
    (X : FiniteMixedSideDistinctClonePropagationFromArc
      T source target incoming) :
    FiniteMixedSideDistinctClonePropagationWithoutPreviousPair
      T source target where
  incoming := incoming
  dependentBlockIndex := X.dependentBlockIndex
  dependentBlock_initial_eq_original := X.dependentBlock_initial_eq_original
  dependentStep := X.dependentStep
  previous := X.previous
  previous_mem_dependent := X.previous_mem_dependent
  previous_mem_prime :=
    ConcretePathDeformation.mem_prime_of_mem_dependentAt
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block X.dependentBlockIndex)
      X.previous_mem_dependent
  previous_anticommutes := X.previous_anticommutes
  previous_finalDegree_three := X.previous_finalDegree_three
  center := X.center
  propagatedNeighbor := X.propagatedNeighbor
  adj_previous := X.adj_previous
  adj_propagatedNeighbor := X.adj_propagatedNeighbor
  previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
  propagatedNeighbor_ne_previousNeighbor :=
    X.propagatedNeighbor_ne_previousNeighbor
  propagatedNeighbor_mem_originalHole :=
    X.propagatedNeighbor_mem_originalHole
  cloneGeometry := X.cloneGeometry

/-- The arc-parameterized finite propagation package still yields the final
claw contradiction. -/
theorem false_of_clawFree
    (X : FiniteMixedSideDistinctClonePropagationFromArc
      T source target incoming)
    (hclaw : G.IsClawFree) : False :=
  X.toPropagationWithoutPreviousPair.false_of_clawFree hclaw

end FiniteMixedSideDistinctClonePropagationFromArc

/-- Same-clone geometry or finite distinct-clone propagation parameterized by
the two actual incoming arcs under comparison. -/
inductive FiniteMixedSideTwoIncomingInteriorGeometryFromArcs
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source source' target : I.Node)
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      FiniteMixedSideTwoIncomingInteriorGeometryFromArcs
        T source source' target incoming incoming'
  | distinctClone :
      (Nonempty
          (FiniteMixedSideDistinctClonePropagationFromArc
            T source target incoming) ∨
        Nonempty
          (FiniteMixedSideDistinctClonePropagationFromArc
            T source' target incoming')) →
      FiniteMixedSideTwoIncomingInteriorGeometryFromArcs
        T source source' target incoming incoming'

/-- Pairwise finite terminal analysis in which incoming arcs are parameters
rather than duplicated fields of the distinct-clone propagation packages. -/
structure FiniteMixedSideTwoIncomingTerminalArcAnalysis
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
        FiniteMixedSideTwoIncomingInteriorGeometryFromArcs
          T source source' target incoming incoming'

namespace FiniteMixedSideTwoIncomingTerminalArcAnalysis

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Convert the arc-parameterized finite analysis to the previous
predecessor-neighbour interface. -/
def toTerminalPreviousNeighborAnalysis
    (A : FiniteMixedSideTwoIncomingTerminalArcAnalysis T) :
    FiniteMixedSideTwoIncomingTerminalPreviousNeighborAnalysis T := by
  refine { interiorGeometry := ?_ }
  intro source source' target hne incoming incoming' hsource hsource'
  rcases A.interiorGeometry
      hne incoming incoming' hsource hsource' with hsame | hdistinct
  · exact
      FiniteMixedSideTwoIncomingInteriorGeometryWithoutPreviousPair.sameClone
        hsame
  · apply
      FiniteMixedSideTwoIncomingInteriorGeometryWithoutPreviousPair.distinctClone
    rcases hdistinct with hleft | hright
    · obtain ⟨X⟩ := hleft
      exact Or.inl ⟨X.toPropagationWithoutPreviousPair⟩
    · obtain ⟨X⟩ := hright
      exact Or.inr ⟨X.toPropagationWithoutPreviousPair⟩

end FiniteMixedSideTwoIncomingTerminalArcAnalysis

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Lemma 14 from a finite terminal analysis whose distinct-clone packages
neither repeat the incoming obstruction arc nor assume prime membership
separately from the concrete dependent-set witness. -/
theorem lemma14_of_terminalArcAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalArcAnalysis T)
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
  T.lemma14_of_terminalPreviousNeighborAnalysis
    A.toTerminalPreviousNeighborAnalysis hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
