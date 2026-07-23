import FreeFermionGraphs.ObstructionSearchTerminalDistinctCloneNeighbors

/-!
# Lemma 14(iv): deriving the alternative clone from the stopping branch

In the distinct-clone branch, the common obstruction target is already known to
be a typed clone of a vertex of the initialized original hole.  That fact is
not independent terminal-propagation data: it follows from the concrete
initial-tether or later-Definition-20 stopping branch, through Lemma 11(a)(ii).

This module removes the chosen clone index and its clone certificate from the
remaining propagation interface.  The search-history geometry is stated
uniformly relative to any original-hole vertex cloned by the target.  The
actual clone witness is then obtained from `InitializationStoppingPairingData`
and used to recover the reduced distinct-clone package from the preceding
module.
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

namespace InitializationTerminalCoreData

/-- Every actual obstruction arc supplies a clone witness for its target in the
initialized original hole.  The witness is derived from the literal stopping
branch, not assumed by the terminal propagation. -/
theorem exists_target_clone_of_incoming
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (h : I.graph.Arc source target) :
    ∃ i : Fin T.executionTrace.originalHole.card,
      T.executionTrace.originalHole.SingleVertexDeformation
        (target : V) i := by
  rcases (T.stoppingPairing.branch h).typedClone_ad hclaw with
    ⟨i, hclone, _hpair⟩
  exact ⟨i, hclone⟩

/-- Choose the clone centre supplied by the concrete stopping branch. -/
noncomputable def targetCloneIndexOfIncoming
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (h : I.graph.Arc source target) :
    Fin T.executionTrace.originalHole.card :=
  Classical.choose (T.exists_target_clone_of_incoming hclaw h)

/-- The chosen stopping-branch index is a genuine clone centre for the target. -/
theorem targetCloneIndexOfIncoming_spec
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (h : I.graph.Arc source target) :
    T.executionTrace.originalHole.SingleVertexDeformation
      (target : V) (T.targetCloneIndexOfIncoming hclaw h) :=
  Classical.choose_spec (T.exists_target_clone_of_incoming hclaw h)

end InitializationTerminalCoreData

/-- Clone-centre facts required by the final distinct-clone contradiction,
stated uniformly relative to any original-hole vertex cloned by the target.

The universal formulation prevents the propagation package from selecting a
clone index independently of the initialized obstruction-search stopping
branch.  Uniqueness of clone centres on an induced hole means this is the same
geometric content as the manuscript's identified vertex `v''`. -/
structure DistinctCloneGeometryRelativeToTarget
    (T : I.InitializationTerminalCoreData)
    (target : I.Node)
    (center previous propagatedNeighbor : V)
    (previousNeighbor0Index previousNeighbor1Index :
      Fin T.executionTrace.originalHole.card) : Prop where
  adj_cloneCenter :
    ∀ (cloneIndex : Fin T.executionTrace.originalHole.card),
      T.executionTrace.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        G.Adj center
          (T.executionTrace.originalHole.vertex cloneIndex)
  previous_ne_cloneCenter :
    ∀ (cloneIndex : Fin T.executionTrace.originalHole.card),
      T.executionTrace.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        previous ≠ T.executionTrace.originalHole.vertex cloneIndex
  propagatedNeighbor_ne_cloneCenter :
    ∀ (cloneIndex : Fin T.executionTrace.originalHole.card),
      T.executionTrace.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        propagatedNeighbor ≠
          T.executionTrace.originalHole.vertex cloneIndex
  cloneCenter_ne_previousNeighbor0 :
    ∀ (cloneIndex : Fin T.executionTrace.originalHole.card),
      T.executionTrace.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        T.executionTrace.originalHole.vertex cloneIndex ≠
          T.executionTrace.originalHole.vertex previousNeighbor0Index
  cloneCenter_ne_previousNeighbor1 :
    ∀ (cloneIndex : Fin T.executionTrace.originalHole.card),
      T.executionTrace.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        T.executionTrace.originalHole.vertex cloneIndex ≠
          T.executionTrace.originalHole.vertex previousNeighbor1Index
  propagatedNeighbor_ne_cycleNeighbor :
    ∀ (cloneIndex q : Fin T.executionTrace.originalHole.card),
      T.executionTrace.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
      G.Adj
          (T.executionTrace.originalHole.vertex cloneIndex)
          (T.executionTrace.originalHole.vertex q) →
        propagatedNeighbor ≠ T.executionTrace.originalHole.vertex q

/-- Remaining distinct-clone propagation data after both the alternative
clone's index and its two cycle neighbours have been removed from the
certificate boundary.

All fields before `cloneGeometry` are literal path-propagation information.
The final field records only how that geometry relates to the clone centre
which the stopping branch will subsequently provide. -/
structure DistinctClonePropagationFromStopping
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
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  propagatedNeighbor_ne_previousNeighbor0 :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex previousNeighbor0Index
  propagatedNeighbor_ne_previousNeighbor1 :
    propagatedNeighbor ≠
      T.executionTrace.originalHole.vertex previousNeighbor1Index
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range T.executionTrace.originalHole.vertex
  cloneGeometry :
    DistinctCloneGeometryRelativeToTarget T target center previous
      propagatedNeighbor previousNeighbor0Index previousNeighbor1Index

namespace DistinctClonePropagationFromStopping

variable {T : I.InitializationTerminalCoreData}
  {source target : I.Node}

/-- Recover the prior reduced propagation package by obtaining the target's
clone centre from the concrete obstruction-search stopping branch. -/
noncomputable def toPropagationWithoutChosenNeighbors
    (X : DistinctClonePropagationFromStopping T source target)
    (hclaw : G.IsClawFree) :
    DistinctClonePropagationWithoutChosenNeighbors T source target := by
  let cloneIndex := T.targetCloneIndexOfIncoming hclaw X.incoming
  have hclone :
      T.executionTrace.originalHole.SingleVertexDeformation
        (target : V) cloneIndex := by
    simpa [cloneIndex] using
      (T.targetCloneIndexOfIncoming_spec hclaw X.incoming)
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
      cloneIndex := cloneIndex
      target_clone := hclone
      previousNeighbor0Index := X.previousNeighbor0Index
      previousNeighbor1Index := X.previousNeighbor1Index
      previousNeighbor0_ne_previousNeighbor1 :=
        X.previousNeighbor0_ne_previousNeighbor1
      adj_previousNeighbor0 := X.adj_previousNeighbor0
      adj_previousNeighbor1 := X.adj_previousNeighbor1
      adj_previous := X.adj_previous
      adj_propagatedNeighbor := X.adj_propagatedNeighbor
      adj_cloneCenter := X.cloneGeometry.adj_cloneCenter cloneIndex hclone
      previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
      previous_ne_cloneCenter :=
        X.cloneGeometry.previous_ne_cloneCenter cloneIndex hclone
      propagatedNeighbor_ne_cloneCenter :=
        X.cloneGeometry.propagatedNeighbor_ne_cloneCenter cloneIndex hclone
      propagatedNeighbor_ne_previousNeighbor0 :=
        X.propagatedNeighbor_ne_previousNeighbor0
      propagatedNeighbor_ne_previousNeighbor1 :=
        X.propagatedNeighbor_ne_previousNeighbor1
      cloneCenter_ne_previousNeighbor0 :=
        X.cloneGeometry.cloneCenter_ne_previousNeighbor0 cloneIndex hclone
      cloneCenter_ne_previousNeighbor1 :=
        X.cloneGeometry.cloneCenter_ne_previousNeighbor1 cloneIndex hclone
      propagatedNeighbor_mem_originalHole :=
        X.propagatedNeighbor_mem_originalHole
      propagatedNeighbor_ne_cycleNeighbor := by
        intro q hAdj
        exact X.cloneGeometry.propagatedNeighbor_ne_cycleNeighbor
          cloneIndex q hclone hAdj }

/-- The distinct-clone contradiction now obtains both the clone centre and its
cycle-neighbour pair from previously formalized obstruction-search data. -/
theorem false_of_clawFree
    (X : DistinctClonePropagationFromStopping T source target)
    (hclaw : G.IsClawFree) : False :=
  (X.toPropagationWithoutChosenNeighbors hclaw).false_of_clawFree hclaw

end DistinctClonePropagationFromStopping

/-- Same-clone geometry or distinct-clone propagation with the clone witness
left entirely to the stopping branch. -/
inductive TwoIncomingInteriorGeometryFromStopping
    (T : I.InitializationTerminalCoreData)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometryFromStopping T source source' target
  | distinctClone :
      (Nonempty (DistinctClonePropagationFromStopping T source target) ∨
        Nonempty (DistinctClonePropagationFromStopping T source' target)) →
      TwoIncomingInteriorGeometryFromStopping T source source' target

/-- Pairwise terminal analysis after removing the alternative clone witness
from the distinct-clone certificate boundary. -/
structure TwoIncomingTerminalStoppingAnalysis
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
        TwoIncomingInteriorGeometryFromStopping T source source' target

namespace TwoIncomingTerminalStoppingAnalysis

variable {T : I.InitializationTerminalCoreData}

/-- Convert the stopping-relative terminal analysis to the preceding
neighbour-relative interface. -/
noncomputable def toTerminalNeighborAnalysis
    (A : TwoIncomingTerminalStoppingAnalysis T)
    (hclaw : G.IsClawFree) :
    TwoIncomingTerminalNeighborAnalysis T where
  interiorGeometry := by
    intro source source' target hne h h' hsource hsource'
    rcases A.interiorGeometry hne h h' hsource hsource' with
      hsame | hdistinct
    · exact TwoIncomingInteriorGeometryWithoutChosenNeighbors.sameClone hsame
    · apply TwoIncomingInteriorGeometryWithoutChosenNeighbors.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationWithoutChosenNeighbors hclaw⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationWithoutChosenNeighbors hclaw⟩

end TwoIncomingTerminalStoppingAnalysis

namespace InitializationTerminalCoreData

/-- Lemma 14 from a terminal analysis whose distinct-clone branch no longer
assumes either a clone index or chosen cycle neighbours for that clone. -/
theorem lemma14_of_terminalStoppingAnalysis
    (T : I.InitializationTerminalCoreData)
    (A : TwoIncomingTerminalStoppingAnalysis T)
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
  exact T.lemma14_of_terminalNeighborAnalysis
    (A.toTerminalNeighborAnalysis hclaw) hclaw

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
