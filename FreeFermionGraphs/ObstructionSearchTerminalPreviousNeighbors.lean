import FreeFermionGraphs.ObstructionSearchTerminalCanonicalClone

/-!
# Lemma 14(iv): deriving the predecessor's original-hole neighbours

Near the end of the distinct-clone branch, the manuscript identifies the
preceding terminal vertex `j_{p-2}` as a first-block dependent vertex of final
degree three.  Lemma 11(a) then shows that its degree on the initialized
original hole is exactly two.  Consequently, its two original-hole neighbours
are not independent propagation data.

This module selects those two neighbours from the degree-two theorem and
removes their indices, distinctness, and adjacency certificates from the
remaining terminal boundary.  The long propagation now records only that the
propagated leaf and the canonical stopping-derived clone centre differ from
every original-hole neighbour of the predecessor.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Two distinct neighbours of a vertex on an indexed induced hole. -/
structure IndexedInducedHole.ExternalNeighborPair
    (C : IndexedInducedHole G) (u : V) where
  left : Fin C.card
  right : Fin C.card
  left_ne_right : left ≠ right
  adj_left : G.Adj u (C.vertex left)
  adj_right : G.Adj u (C.vertex right)

/-- External degree two supplies a pair containing exactly the two
original-hole neighbours. -/
theorem IndexedInducedHole.externalNeighborPair_nonempty
    (C : IndexedInducedHole G) {u : V}
    (hdegree : C.externalDegree u = 2) :
    Nonempty (C.ExternalNeighborPair u) := by
  have hcard : (C.neighborIndexSet u).ncard = 2 := by
    simpa [IndexedInducedHole.externalDegree] using hdegree
  obtain ⟨left, right, hne, hset⟩ := Set.ncard_eq_two.mp hcard
  have hleft : left ∈ C.neighborIndexSet u := by
    rw [hset]
    simp
  have hright : right ∈ C.neighborIndexSet u := by
    rw [hset]
    simp
  exact ⟨
    { left := left
      right := right
      left_ne_right := hne
      adj_left := hleft
      adj_right := hright }⟩

/-- A fixed pair of the two original-hole neighbours of a degree-two vertex. -/
noncomputable def IndexedInducedHole.externalNeighborPair
    (C : IndexedInducedHole G) (u : V)
    (hdegree : C.externalDegree u = 2) :
    C.ExternalNeighborPair u :=
  Classical.choice (C.externalNeighborPair_nonempty hdegree)

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- Canonical-clone geometry after removing the chosen neighbour pair of the
preceding terminal vertex. -/
structure DistinctCloneGeometryWithoutPreviousPair
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source target : I.Node)
    (incoming : I.graph.Arc source target)
    (center previous propagatedNeighbor : V) : Prop where
  adj_cloneCenter :
    G.Adj center
      (T.executionTrace.originalHole.vertex
        (T.targetCloneIndexOfIncoming hclaw incoming))
  previous_ne_cloneCenter :
    previous ≠
      T.executionTrace.originalHole.vertex
        (T.targetCloneIndexOfIncoming hclaw incoming)
  propagatedNeighbor_ne_cloneCenter :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex
        (T.targetCloneIndexOfIncoming hclaw incoming)
  cloneCenter_ne_previousNeighbor :
    ∀ q : Fin T.executionTrace.originalHole.card,
      G.Adj previous (T.executionTrace.originalHole.vertex q) →
        T.executionTrace.originalHole.vertex
            (T.targetCloneIndexOfIncoming hclaw incoming) ≠
          T.executionTrace.originalHole.vertex q
  propagatedNeighbor_ne_cycleNeighbor :
    ∀ q : Fin T.executionTrace.originalHole.card,
      G.Adj
          (T.executionTrace.originalHole.vertex
            (T.targetCloneIndexOfIncoming hclaw incoming))
          (T.executionTrace.originalHole.vertex q) →
        propagatedNeighbor ≠ T.executionTrace.originalHole.vertex q

/-- Remaining distinct-clone propagation data without a chosen pair of
original-hole neighbours for the predecessor. -/
structure DistinctClonePropagationWithoutPreviousPair
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source target : I.Node) where
  incoming : I.graph.Arc source target
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
  previous_mem_prime : previous ∈ Cprime
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

namespace DistinctClonePropagationWithoutPreviousPair

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}
  {source target : I.Node}

/-- The predecessor has original-hole degree two by its concrete first-block
Definition 20 witness. -/
theorem previous_originalDegree_two
    (X : DistinctClonePropagationWithoutPreviousPair T hclaw source target) :
    T.executionTrace.originalHole.externalDegree X.previous = 2 :=
  OrderedOSExecution.originalDegree_two_of_firstBlock_dependent
    (T.executionTrace.execution source)
    hclaw X.dependentBlockIndex X.dependentBlock_is_first
    X.previous_mem_dependent X.previous_mem_prime
    X.previous_anticommutes X.previous_finalDegree_three

/-- Select the predecessor's two neighbours from its derived degree and recover
the canonical-clone propagation package. -/
noncomputable def toPropagationAtStoppingClone
    (X : DistinctClonePropagationWithoutPreviousPair T hclaw source target) :
    DistinctClonePropagationAtStoppingClone T hclaw source target := by
  let B := T.executionTrace.originalHole.externalNeighborPair
    X.previous X.previous_originalDegree_two
  exact
    { incoming := X.incoming
      dependentBlockIndex := X.dependentBlockIndex
      dependentBlock_is_first := X.dependentBlock_is_first
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
          previous_ne_cloneCenter :=
            X.cloneGeometry.previous_ne_cloneCenter
          propagatedNeighbor_ne_cloneCenter :=
            X.cloneGeometry.propagatedNeighbor_ne_cloneCenter
          cloneCenter_ne_previousNeighbor0 :=
            X.cloneGeometry.cloneCenter_ne_previousNeighbor B.left B.adj_left
          cloneCenter_ne_previousNeighbor1 :=
            X.cloneGeometry.cloneCenter_ne_previousNeighbor B.right B.adj_right
          propagatedNeighbor_ne_cycleNeighbor :=
            X.cloneGeometry.propagatedNeighbor_ne_cycleNeighbor } }

/-- The pair-free package still yields the manuscript's final claw
contradiction. -/
theorem false_of_clawFree
    (X : DistinctClonePropagationWithoutPreviousPair T hclaw source target) :
    False :=
  X.toPropagationAtStoppingClone.false_of_clawFree

end DistinctClonePropagationWithoutPreviousPair

/-- Same-clone geometry or distinct-clone propagation without a chosen
predecessor-neighbour pair. -/
inductive TwoIncomingInteriorGeometryWithoutPreviousPair
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometryWithoutPreviousPair
        T hclaw source source' target
  | distinctClone :
      (Nonempty
          (DistinctClonePropagationWithoutPreviousPair T hclaw source target) ∨
        Nonempty
          (DistinctClonePropagationWithoutPreviousPair T hclaw source' target)) →
      TwoIncomingInteriorGeometryWithoutPreviousPair
        T hclaw source source' target

/-- Pairwise terminal analysis after eliminating the predecessor's chosen
original-hole neighbour pair. -/
structure TwoIncomingTerminalPreviousNeighborAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        TwoIncomingInteriorGeometryWithoutPreviousPair
          T hclaw source source' target

namespace TwoIncomingTerminalPreviousNeighborAnalysis

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}

/-- Convert the pair-free terminal analysis to the canonical-clone interface. -/
noncomputable def toTerminalCanonicalCloneAnalysis
    (A : TwoIncomingTerminalPreviousNeighborAnalysis T hclaw) :
    TwoIncomingTerminalCanonicalCloneAnalysis T hclaw where
  interiorGeometry := by
    intro source source' target hne h h' hsource hsource'
    rcases A.interiorGeometry hne h h' hsource hsource' with
      hsame | hdistinct
    · exact TwoIncomingInteriorGeometryAtStoppingClone.sameClone hsame
    · apply TwoIncomingInteriorGeometryAtStoppingClone.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationAtStoppingClone⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationAtStoppingClone⟩

end TwoIncomingTerminalPreviousNeighborAnalysis

namespace InitializationTerminalCoreData

/-- Lemma 14 from a terminal analysis in which neither the stopping clone's
cycle neighbours nor the predecessor's original-hole neighbours are selected
as primitive certificate data. -/
theorem lemma14_of_terminalPreviousNeighborAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (A : TwoIncomingTerminalPreviousNeighborAnalysis T hclaw) :
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
  exact T.lemma14_of_terminalCanonicalCloneAnalysis hclaw
    A.toTerminalCanonicalCloneAnalysis

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
