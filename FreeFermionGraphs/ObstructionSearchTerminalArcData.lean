import FreeFermionGraphs.ObstructionSearchTerminalPreviousNeighbors

/-!
# Lemma 14(iv): deriving prime membership and incoming-arc data

The remaining distinct-clone propagation package still repeated two facts that
are already determined by its context.

First, membership in a Definition 20 dependent set includes membership in the
prime set `Cprime` by definition.  Second, the incoming obstruction arc is one
of the arguments of the pairwise terminal analysis and need not be stored again
inside the propagation certificate.

This module derives prime membership from the concrete dependent-set witness
and parameterizes the distinct-clone package by the actual incoming arc.  The
long two-search argument is left responsible only for the genuinely geometric
propagation data.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G}

/-- Membership in a concrete Definition 20 dependent set already implies
membership in the prime set. -/
theorem mem_prime_of_mem_dependentAt
    (D : ConcretePathDeformation O Cprime)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    u ∈ Cprime := by
  have huStep := D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    ((D.deformation.step
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩).mem_dependentSet).1 huStep
  exact hmem.1

end ConcretePathDeformation

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Remaining distinct-clone propagation data parameterized by the actual
incoming obstruction arc.

The package no longer stores the incoming arc or prime-set membership of the
predecessor.  The former is a parameter supplied by the pairwise terminal
analysis, while the latter follows from `previous_mem_dependent`. -/
structure DistinctClonePropagationFromArc
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  dependentBlockIndex :
    Fin (T.executionTrace.execution source).blockCount
  dependentBlock_is_first :
    ∃ F :
        ((T.executionTrace.execution source).concreteBlock
          dependentBlockIndex).FullDefinition19Lemma11AData,
      (T.executionTrace.execution source).blockContext
          dependentBlockIndex =
        ConcretePathDeformation.Lemma11AHistoryContext.first F
  dependentStep : Nat
  previous : V
  previous_mem_dependent :
    previous ∈
      ((T.executionTrace.execution source).concreteBlock
        dependentBlockIndex).dependentAt dependentStep
  previous_anticommutes :
    ((T.executionTrace.execution source).concreteBlock
      dependentBlockIndex).path.AnticommutesWith previous
  previous_finalDegree_three :
    ((T.executionTrace.execution source).concreteBlock
      dependentBlockIndex).finalHole.externalDegree previous = 3
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

namespace DistinctClonePropagationFromArc

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- Recover the previous propagation interface, deriving prime membership from
the concrete dependent-set witness and reusing the incoming arc parameter. -/
def toPropagationWithoutPreviousPair
    (X : DistinctClonePropagationFromArc T hclaw source target incoming) :
    DistinctClonePropagationWithoutPreviousPair T hclaw source target where
  incoming := incoming
  dependentBlockIndex := X.dependentBlockIndex
  dependentBlock_is_first := X.dependentBlock_is_first
  dependentStep := X.dependentStep
  previous := X.previous
  previous_mem_dependent := X.previous_mem_dependent
  previous_mem_prime :=
    ConcretePathDeformation.mem_prime_of_mem_dependentAt
      ((T.executionTrace.execution source).concreteBlock
        X.dependentBlockIndex)
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

/-- The arc-parameterized propagation package still yields the final claw
contradiction. -/
theorem false_of_clawFree
    (X : DistinctClonePropagationFromArc T hclaw source target incoming) :
    False :=
  X.toPropagationWithoutPreviousPair.false_of_clawFree

end DistinctClonePropagationFromArc

/-- Same-clone geometry or distinct-clone propagation parameterized by the two
actual incoming arcs under comparison. -/
inductive TwoIncomingInteriorGeometryFromArcs
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source source' target : I.Node)
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometryFromArcs
        T hclaw source source' target incoming incoming'
  | distinctClone :
      (Nonempty
          (DistinctClonePropagationFromArc
            T hclaw source target incoming) ∨
        Nonempty
          (DistinctClonePropagationFromArc
            T hclaw source' target incoming')) →
      TwoIncomingInteriorGeometryFromArcs
        T hclaw source source' target incoming incoming'

/-- Pairwise terminal analysis in which the incoming arcs are parameters rather
than duplicated fields of the distinct-clone certificates. -/
structure TwoIncomingTerminalArcAnalysis
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
        TwoIncomingInteriorGeometryFromArcs
          T hclaw source source' target incoming incoming'

namespace TwoIncomingTerminalArcAnalysis

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}

/-- Convert the arc-parameterized pairwise analysis to the previous
predecessor-neighbour interface. -/
theorem toTerminalPreviousNeighborAnalysis
    (A : TwoIncomingTerminalArcAnalysis T hclaw) :
    TwoIncomingTerminalPreviousNeighborAnalysis T hclaw := by
  refine { interiorGeometry := ?_ }
  intro source source' target hne incoming incoming' hsource hsource'
  rcases A.interiorGeometry hne incoming incoming' hsource hsource' with
    hsame | hdistinct
  · exact TwoIncomingInteriorGeometryWithoutPreviousPair.sameClone hsame
  · apply TwoIncomingInteriorGeometryWithoutPreviousPair.distinctClone
    rcases hdistinct with hleft | hright
    · obtain ⟨X⟩ := hleft
      exact Or.inl ⟨X.toPropagationWithoutPreviousPair⟩
    · obtain ⟨X⟩ := hright
      exact Or.inr ⟨X.toPropagationWithoutPreviousPair⟩

end TwoIncomingTerminalArcAnalysis

namespace InitializationTerminalCoreData

/-- Lemma 14 from a terminal analysis whose distinct-clone certificates neither
repeat the incoming obstruction arc nor assume prime membership separately from
their concrete dependent-set witness. -/
theorem lemma14_of_terminalArcAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (A : TwoIncomingTerminalArcAnalysis T hclaw) :
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
  exact T.lemma14_of_terminalPreviousNeighborAnalysis hclaw
    A.toTerminalPreviousNeighborAnalysis

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
