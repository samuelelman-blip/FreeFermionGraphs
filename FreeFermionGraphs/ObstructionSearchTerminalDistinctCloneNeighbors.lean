import FreeFermionGraphs.ObstructionSearchTerminalDistinctClone

/-!
# Lemma 14(iv): deriving the alternative clone's hole neighbours

The final distinct-clone paragraph of Lemma 14 names `b₀,b₁` as the two
original-hole neighbours of the alternative clone `v''`.  They are not
independent obstruction-search data: once `v''` is identified as a vertex of
the initialized induced hole, the cyclic hole structure supplies such a pair.

This module removes the chosen indices and cyclic-adjacency certificates for
`b₀,b₁` from the remaining distinct-clone propagation interface.  The search
propagation only records that the propagated leaf is different from every
hole neighbour of the alternative clone.  A canonical pair is then selected
from the indexed hole and converted to the terminal neighbourhood used by the
existing claw contradiction.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Two distinct cycle neighbours of one vertex of an indexed induced hole.

The pair is data rather than a proposition so it can be selected once and
reused when constructing the final distinct-clone neighbourhood. -/
structure IndexedInducedHole.CycleNeighborPair
    (C : IndexedInducedHole G) (i : Fin C.card) where
  left : Fin C.card
  right : Fin C.card
  left_ne_right : left ≠ right
  adj_left : G.Adj (C.vertex i) (C.vertex left)
  adj_right : G.Adj (C.vertex i) (C.vertex right)

/-- Every indexed hole vertex has a pair of distinct cycle neighbours. -/
theorem IndexedInducedHole.cycleNeighborPair_nonempty
    (C : IndexedInducedHole G) (i : Fin C.card) :
    Nonempty (IndexedInducedHole.CycleNeighborPair C i) := by
  obtain ⟨left, right, hne, hleft, hright, _hnonadj⟩ :=
    C.exists_two_nonadjacent_neighbors i
  exact ⟨
    { left := left
      right := right
      left_ne_right := hne
      adj_left := hleft
      adj_right := hright }⟩

/-- A fixed pair of the two cycle neighbours of an indexed hole vertex. -/
noncomputable def IndexedInducedHole.cycleNeighborPair
    (C : IndexedInducedHole G) (i : Fin C.card) :
    IndexedInducedHole.CycleNeighborPair C i :=
  Classical.choice (C.cycleNeighborPair_nonempty i)

namespace FixedPairingPathFamily

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

/-- The remaining distinct-clone propagation data without a preselected
`b₀,b₁` pair.

The alternative clone is still tied to the manuscript relation
`j'' ≺_C v''`.  Its two neighbours on the original hole are now derived from
the indexed cycle.  The last field is the propagated inequality established
by the long search-history argument: the propagated original-hole leaf is not
one of those cycle neighbours.  It does not assume the resulting nonedge. -/
structure DistinctClonePropagationWithoutChosenNeighbors
    (T : I.InitializationTerminalCoreData)
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
  cloneIndex : Fin T.executionTrace.originalHole.card
  target_clone :
    T.executionTrace.originalHole.SingleVertexDeformation
      (target : V) cloneIndex
  previousNeighbor0Index : Fin T.executionTrace.originalHole.card
  previousNeighbor1Index : Fin T.executionTrace.originalHole.card
  previousNeighbor0_ne_previousNeighbor1 :
    previousNeighbor0Index ≠ previousNeighbor1Index
  adj_previousNeighbor0 :
    G.Adj previous
      (T.executionTrace.originalHole.vertex previousNeighbor0Index)
  adj_previousNeighbor1 :
    G.Adj previous
      (T.executionTrace.originalHole.vertex previousNeighbor1Index)
  adj_previous : G.Adj center previous
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  adj_cloneCenter :
    G.Adj center (T.executionTrace.originalHole.vertex cloneIndex)
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  previous_ne_cloneCenter :
    previous ≠ T.executionTrace.originalHole.vertex cloneIndex
  propagatedNeighbor_ne_cloneCenter :
    propagatedNeighbor ≠ T.executionTrace.originalHole.vertex cloneIndex
  propagatedNeighbor_ne_previousNeighbor0 :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex previousNeighbor0Index
  propagatedNeighbor_ne_previousNeighbor1 :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex previousNeighbor1Index
  cloneCenter_ne_previousNeighbor0 :
    T.executionTrace.originalHole.vertex cloneIndex ≠
      T.executionTrace.originalHole.vertex previousNeighbor0Index
  cloneCenter_ne_previousNeighbor1 :
    T.executionTrace.originalHole.vertex cloneIndex ≠
      T.executionTrace.originalHole.vertex previousNeighbor1Index
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range T.executionTrace.originalHole.vertex
  propagatedNeighbor_ne_cycleNeighbor :
    ∀ q : Fin T.executionTrace.originalHole.card,
      G.Adj
          (T.executionTrace.originalHole.vertex cloneIndex)
          (T.executionTrace.originalHole.vertex q) →
        propagatedNeighbor ≠ T.executionTrace.originalHole.vertex q

namespace DistinctClonePropagationWithoutChosenNeighbors

variable {T : I.InitializationTerminalCoreData}
  {source target : I.Node}

/-- Select the two cycle neighbours of the alternative clone and recover the
existing execution-level propagation object. -/
noncomputable def toPropagationData
    (X : DistinctClonePropagationWithoutChosenNeighbors T source target) :
    DistinctClonePropagationData T source target := by
  let B :=
    T.executionTrace.originalHole.cycleNeighborPair X.cloneIndex
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
      cloneNeighbor0_cyclic :=
        (T.executionTrace.originalHole.adj_iff X.cloneIndex B.left).1
          B.adj_left
      cloneNeighbor1_cyclic :=
        (T.executionTrace.originalHole.adj_iff X.cloneIndex B.right).1
          B.adj_right
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

/-- The reduced propagation package still yields the manuscript's final claw
contradiction, with `b₀,b₁` derived from the original hole. -/
theorem false_of_clawFree
    (X : DistinctClonePropagationWithoutChosenNeighbors T source target)
    (hclaw : G.IsClawFree) : False :=
  X.toPropagationData.false_of_clawFree hclaw

end DistinctClonePropagationWithoutChosenNeighbors

/-- The same-clone alternative together with the reduced distinct-clone
propagation interface. -/
inductive TwoIncomingInteriorGeometryWithoutChosenNeighbors
    (T : I.InitializationTerminalCoreData)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometryWithoutChosenNeighbors
        T source source' target
  | distinctClone :
      (Nonempty
          (DistinctClonePropagationWithoutChosenNeighbors T source target) ∨
        Nonempty
          (DistinctClonePropagationWithoutChosenNeighbors T source' target)) →
      TwoIncomingInteriorGeometryWithoutChosenNeighbors
        T source source' target

/-- Pairwise terminal analysis in which the alternative clone's two
original-hole neighbours are not supplied as chosen data. -/
structure TwoIncomingTerminalNeighborAnalysis
    (T : I.InitializationTerminalCoreData) : Prop where
  interiorGeometry :
    ∀ ⦃source source' target : I.Node⦄,
      source ≠ source' →
      I.graph.Arc source target →
      I.graph.Arc source' target →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        TwoIncomingInteriorGeometryWithoutChosenNeighbors
          T source source' target

namespace TwoIncomingTerminalNeighborAnalysis

variable {T : I.InitializationTerminalCoreData}

/-- Convert the reduced pairwise analysis to the previously integrated
terminal-claw interface. -/
noncomputable def toTerminalClawAnalysis
    (A : TwoIncomingTerminalNeighborAnalysis T) :
    TwoIncomingTerminalClawAnalysis T where
  interiorGeometry := by
    intro source source' target hne h h' hsource hsource'
    rcases A.interiorGeometry hne h h' hsource hsource' with
      hsame | hdistinct
    · exact TwoIncomingInteriorGeometry.sameClone hsame
    · apply TwoIncomingInteriorGeometry.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationData⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationData⟩

end TwoIncomingTerminalNeighborAnalysis

namespace InitializationTerminalCoreData

/-- Lemma 14 from the terminal core and a pairwise analysis that leaves the
choice of the alternative clone's two hole neighbours to the indexed cycle. -/
theorem lemma14_of_terminalNeighborAnalysis
    (T : I.InitializationTerminalCoreData)
    (A : TwoIncomingTerminalNeighborAnalysis T)
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
              I.dependentSet source' = {(target : V)}))) := by
  exact T.lemma14_of_terminalClawAnalysis
    A.toTerminalClawAnalysis hclaw

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
