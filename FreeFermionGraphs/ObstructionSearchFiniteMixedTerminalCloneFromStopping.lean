import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalDistinctCloneNeighbors

/-!
# Deriving the finite alternative clone from the stopping branch

For every actual obstruction arc, the literal initial-tether or later
Definition 20 stopping branch already proves that the target is a typed clone
of a vertex of the initialized original hole.  The distinct-clone propagation
must therefore not select an unrelated clone index.

This module removes the clone index and clone certificate from the finite
propagation boundary.  The remaining geometry is formulated uniformly for
any original-hole vertex cloned by the target.  The actual clone witness is
then obtained from the finite stopping branch.
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

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Every finite obstruction arc supplies a clone witness for its target in
the initialized original hole. -/
theorem exists_target_clone_of_incoming
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    ∃ i : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
        (target : V) i := by
  rcases (T.stoppingPairing.branch incoming).typedClone_ad hclaw with
    ⟨i, hclone, _hpair⟩
  exact ⟨i, hclone⟩

/-- Choose the target clone centre supplied by the finite stopping branch. -/
noncomputable def targetCloneIndexOfIncoming
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Fin T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card :=
  Classical.choose (T.exists_target_clone_of_incoming hclaw incoming)

/-- The chosen finite stopping-branch index is a genuine clone centre. -/
theorem targetCloneIndexOfIncoming_spec
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
      (target : V) (T.targetCloneIndexOfIncoming hclaw incoming) :=
  Classical.choose_spec (T.exists_target_clone_of_incoming hclaw incoming)

end InitializationFiniteMixedSideTerminalCoreData

/-- Clone-centre relations needed by the final finite distinct-clone
contradiction, stated uniformly for any original-hole centre cloned by the
target. -/
structure FiniteMixedSideDistinctCloneGeometryRelativeToTarget
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (target : I.Node)
    (center previous propagatedNeighbor : V)
    (previousNeighbor0Index previousNeighbor1Index : Fin
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card) :
    Prop where
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
  cloneCenter_ne_previousNeighbor0 :
    ∀ cloneIndex : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            cloneIndex ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            previousNeighbor0Index
  cloneCenter_ne_previousNeighbor1 :
    ∀ cloneIndex : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
          (target : V) cloneIndex →
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            cloneIndex ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
            previousNeighbor1Index
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

/-- Finite distinct-clone propagation after removing both the target clone
index and its selected cycle-neighbour pair from the certificate boundary. -/
structure FiniteMixedSideDistinctClonePropagationFromStopping
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
  previous_ne_propagatedNeighbor : previous ≠ propagatedNeighbor
  propagatedNeighbor_ne_previousNeighbor0 :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor0Index
  propagatedNeighbor_ne_previousNeighbor1 :
    propagatedNeighbor ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        previousNeighbor1Index
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  cloneGeometry :
    FiniteMixedSideDistinctCloneGeometryRelativeToTarget
      T target center previous propagatedNeighbor
      previousNeighbor0Index previousNeighbor1Index

namespace FiniteMixedSideDistinctClonePropagationFromStopping

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}

/-- Recover the reduced finite propagation package by obtaining the target's
clone centre from the literal finite stopping branch. -/
noncomputable def toPropagationWithoutChosenNeighbors
    (X : FiniteMixedSideDistinctClonePropagationFromStopping T source target)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideDistinctClonePropagationWithoutChosenNeighbors
      T source target := by
  let cloneIndex := T.targetCloneIndexOfIncoming hclaw X.incoming
  have hclone :
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.SingleVertexDeformation
        (target : V) cloneIndex := by
    simpa [cloneIndex] using
      (T.targetCloneIndexOfIncoming_spec hclaw X.incoming)
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

/-- The finite distinct-clone contradiction now obtains the clone centre and
its two cycle neighbours from previously formalized stopping data. -/
theorem false_of_clawFree
    (X : FiniteMixedSideDistinctClonePropagationFromStopping T source target)
    (hclaw : G.IsClawFree) : False :=
  (X.toPropagationWithoutChosenNeighbors hclaw).false_of_clawFree hclaw

end FiniteMixedSideDistinctClonePropagationFromStopping

/-- Same-clone geometry or finite distinct-clone propagation with the clone
witness supplied entirely by the stopping branch. -/
inductive FiniteMixedSideTwoIncomingInteriorGeometryFromStopping
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      FiniteMixedSideTwoIncomingInteriorGeometryFromStopping
        T source source' target
  | distinctClone :
      (Nonempty
          (FiniteMixedSideDistinctClonePropagationFromStopping
            T source target) ∨
        Nonempty
          (FiniteMixedSideDistinctClonePropagationFromStopping
            T source' target)) →
      FiniteMixedSideTwoIncomingInteriorGeometryFromStopping
        T source source' target

/-- Pairwise finite terminal analysis after removing the target clone witness
from the distinct-clone propagation boundary. -/
structure FiniteMixedSideTwoIncomingTerminalStoppingAnalysis
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
        FiniteMixedSideTwoIncomingInteriorGeometryFromStopping
          T source source' target

namespace FiniteMixedSideTwoIncomingTerminalStoppingAnalysis

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Convert the stopping-relative finite analysis to the preceding
neighbour-relative interface. -/
noncomputable def toTerminalNeighborAnalysis
    (A : FiniteMixedSideTwoIncomingTerminalStoppingAnalysis T)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideTwoIncomingTerminalNeighborAnalysis T where
  interiorGeometry := by
    intro source source' target hne incoming incoming' hsource hsource'
    rcases A.interiorGeometry
        hne incoming incoming' hsource hsource' with hsame | hdistinct
    · exact
        FiniteMixedSideTwoIncomingInteriorGeometryWithoutChosenNeighbors.sameClone
          hsame
    · apply
        FiniteMixedSideTwoIncomingInteriorGeometryWithoutChosenNeighbors.distinctClone
      rcases hdistinct with hleft | hright
      · obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationWithoutChosenNeighbors hclaw⟩
      · obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationWithoutChosenNeighbors hclaw⟩

end FiniteMixedSideTwoIncomingTerminalStoppingAnalysis

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Lemma 14 from a finite terminal analysis whose distinct-clone branch no
longer assumes either a clone index or chosen cycle neighbours. -/
theorem lemma14_of_terminalStoppingAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalStoppingAnalysis T)
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
  T.lemma14_of_terminalNeighborAnalysis
    (A.toTerminalNeighborAnalysis hclaw) hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
