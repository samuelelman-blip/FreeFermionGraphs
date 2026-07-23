import FreeFermionGraphs.ObstructionSearchTerminalCloneFromStopping

/-!
# Lemma 14(iv): canonical stopping-branch clone centre

For each obstruction arc, the stopping branch determines a clone centre for the
obstruction target in the initialized original hole.  The centre is unique,
because one vertex cannot clone two different vertices of an induced hole.

This module uses that uniqueness to replace the universal clone-centre fields of
`DistinctCloneGeometryRelativeToTarget` by facts stated only at the canonical
stopping-derived centre.  Thus the remaining long-propagation boundary no
longer quantifies over every possible clone witness.
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

/-- The stopping-derived clone index of a fixed obstruction target is
independent of which incoming obstruction arc is used to obtain it. -/
theorem targetCloneIndexOfIncoming_eq
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (h : I.graph.Arc source target)
    (h' : I.graph.Arc source' target) :
    T.targetCloneIndexOfIncoming hclaw h =
      T.targetCloneIndexOfIncoming hclaw h' := by
  exact
    (T.targetCloneIndexOfIncoming_spec hclaw h).center_eq
      (T.targetCloneIndexOfIncoming_spec hclaw h')

/-- Any clone witness for the target has the same centre as the canonical
stopping-derived witness. -/
theorem cloneIndex_eq_targetCloneIndexOfIncoming
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (h : I.graph.Arc source target)
    {i : Fin T.executionTrace.originalHole.card}
    (hi : T.executionTrace.originalHole.SingleVertexDeformation
      (target : V) i) :
    i = T.targetCloneIndexOfIncoming hclaw h := by
  exact hi.center_eq (T.targetCloneIndexOfIncoming_spec hclaw h)

end InitializationTerminalCoreData

/-- Final distinct-clone facts stated only at the canonical clone centre selected
by the concrete stopping branch. -/
structure DistinctCloneGeometryAtStoppingClone
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source target : I.Node)
    (incoming : I.graph.Arc source target)
    (center previous propagatedNeighbor : V)
    (previousNeighbor0Index previousNeighbor1Index :
      Fin T.executionTrace.originalHole.card) : Prop where
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
  cloneCenter_ne_previousNeighbor0 :
    T.executionTrace.originalHole.vertex
        (T.targetCloneIndexOfIncoming hclaw incoming) ≠
      T.executionTrace.originalHole.vertex previousNeighbor0Index
  cloneCenter_ne_previousNeighbor1 :
    T.executionTrace.originalHole.vertex
        (T.targetCloneIndexOfIncoming hclaw incoming) ≠
      T.executionTrace.originalHole.vertex previousNeighbor1Index
  propagatedNeighbor_ne_cycleNeighbor :
    ∀ q : Fin T.executionTrace.originalHole.card,
      G.Adj
          (T.executionTrace.originalHole.vertex
            (T.targetCloneIndexOfIncoming hclaw incoming))
          (T.executionTrace.originalHole.vertex q) →
        propagatedNeighbor ≠ T.executionTrace.originalHole.vertex q

namespace DistinctCloneGeometryAtStoppingClone

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}
  {center previous propagatedNeighbor : V}
  {previousNeighbor0Index previousNeighbor1Index :
    Fin T.executionTrace.originalHole.card}

/-- Uniqueness of the clone centre promotes facts at the canonical
stopping-derived centre to the prior target-relative interface. -/
theorem toRelative
    (X : DistinctCloneGeometryAtStoppingClone T hclaw source target incoming
      center previous propagatedNeighbor
      previousNeighbor0Index previousNeighbor1Index) :
    DistinctCloneGeometryRelativeToTarget T target center previous
      propagatedNeighbor previousNeighbor0Index previousNeighbor1Index := by
  refine
    { adj_cloneCenter := ?_
      previous_ne_cloneCenter := ?_
      propagatedNeighbor_ne_cloneCenter := ?_
      cloneCenter_ne_previousNeighbor0 := ?_
      cloneCenter_ne_previousNeighbor1 := ?_
      propagatedNeighbor_ne_cycleNeighbor := ?_ }
  · intro cloneIndex hclone
    have hEq := T.cloneIndex_eq_targetCloneIndexOfIncoming
      hclaw incoming hclone
    simpa [hEq] using X.adj_cloneCenter
  · intro cloneIndex hclone
    have hEq := T.cloneIndex_eq_targetCloneIndexOfIncoming
      hclaw incoming hclone
    simpa [hEq] using X.previous_ne_cloneCenter
  · intro cloneIndex hclone
    have hEq := T.cloneIndex_eq_targetCloneIndexOfIncoming
      hclaw incoming hclone
    simpa [hEq] using X.propagatedNeighbor_ne_cloneCenter
  · intro cloneIndex hclone
    have hEq := T.cloneIndex_eq_targetCloneIndexOfIncoming
      hclaw incoming hclone
    simpa [hEq] using X.cloneCenter_ne_previousNeighbor0
  · intro cloneIndex hclone
    have hEq := T.cloneIndex_eq_targetCloneIndexOfIncoming
      hclaw incoming hclone
    simpa [hEq] using X.cloneCenter_ne_previousNeighbor1
  · intro cloneIndex q hclone hAdj
    have hEq := T.cloneIndex_eq_targetCloneIndexOfIncoming
      hclaw incoming hclone
    subst cloneIndex
    exact X.propagatedNeighbor_ne_cycleNeighbor q hAdj

end DistinctCloneGeometryAtStoppingClone

/-- Remaining distinct-clone propagation data with all clone-centre geometry
stated at the canonical stopping-derived centre. -/
structure DistinctClonePropagationAtStoppingClone
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
    DistinctCloneGeometryAtStoppingClone T hclaw source target incoming
      center previous propagatedNeighbor
      previousNeighbor0Index previousNeighbor1Index

namespace DistinctClonePropagationAtStoppingClone

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}
  {source target : I.Node}

/-- Convert the canonical-centre propagation package to the previous
stopping-relative package. -/
def toPropagationFromStopping
    (X : DistinctClonePropagationAtStoppingClone T hclaw source target) :
    DistinctClonePropagationFromStopping T source target where
  incoming := X.incoming
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
  previousNeighbor0Index := X.previousNeighbor0Index
  previousNeighbor1Index := X.previousNeighbor1Index
  previousNeighbor0_ne_previousNeighbor1 :=
    X.previousNeighbor0_ne_previousNeighbor1
  adj_previousNeighbor0 := X.adj_previousNeighbor0
  adj_previousNeighbor1 := X.adj_previousNeighbor1
  adj_previous := X.adj_previous
  adj_propagatedNeighbor := X.adj_propagatedNeighbor
  previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
  propagatedNeighbor_ne_previousNeighbor0 :=
    X.propagatedNeighbor_ne_previousNeighbor0
  propagatedNeighbor_ne_previousNeighbor1 :=
    X.propagatedNeighbor_ne_previousNeighbor1
  propagatedNeighbor_mem_originalHole := X.propagatedNeighbor_mem_originalHole
  cloneGeometry := X.cloneGeometry.toRelative

/-- The canonical stopping-centre package still yields the final claw
contradiction. -/
theorem false_of_clawFree
    (X : DistinctClonePropagationAtStoppingClone T hclaw source target) :
    False :=
  X.toPropagationFromStopping.false_of_clawFree hclaw

end DistinctClonePropagationAtStoppingClone

/-- Same-clone geometry or distinct-clone propagation expressed at the
canonical stopping-derived clone centre. -/
inductive TwoIncomingInteriorGeometryAtStoppingClone
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (source source' target : I.Node) : Prop where
  | sameClone :
      Nonempty
        ((T.terminalPath target).SameCloneTerminalNeighborhood (target : V)) →
      TwoIncomingInteriorGeometryAtStoppingClone
        T hclaw source source' target
  | distinctClone :
      (Nonempty
          (DistinctClonePropagationAtStoppingClone T hclaw source target) ∨
        Nonempty
          (DistinctClonePropagationAtStoppingClone T hclaw source' target)) →
      TwoIncomingInteriorGeometryAtStoppingClone
        T hclaw source source' target

/-- Pairwise terminal analysis whose distinct-clone branch uses only the
canonical stopping-derived clone centre. -/
structure TwoIncomingTerminalCanonicalCloneAnalysis
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
        TwoIncomingInteriorGeometryAtStoppingClone
          T hclaw source source' target

namespace TwoIncomingTerminalCanonicalCloneAnalysis

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}

/-- Convert the canonical-centre pairwise analysis to the previous
stopping-relative interface. -/
theorem toTerminalStoppingAnalysis
    (A : TwoIncomingTerminalCanonicalCloneAnalysis T hclaw) :
    TwoIncomingTerminalStoppingAnalysis T := by
  refine { interiorGeometry := ?_ }
  intro source source' target hne h h' hsource hsource'
  rcases A.interiorGeometry hne h h' hsource hsource' with
    hsame | hdistinct
  · exact TwoIncomingInteriorGeometryFromStopping.sameClone hsame
  · apply TwoIncomingInteriorGeometryFromStopping.distinctClone
    rcases hdistinct with hleft | hright
    · obtain ⟨X⟩ := hleft
      exact Or.inl ⟨X.toPropagationFromStopping⟩
    · obtain ⟨X⟩ := hright
      exact Or.inr ⟨X.toPropagationFromStopping⟩

end TwoIncomingTerminalCanonicalCloneAnalysis

namespace InitializationTerminalCoreData

/-- Lemma 14 from a terminal analysis whose distinct-clone geometry is stated
only at the unique stopping-derived clone centre. -/
theorem lemma14_of_terminalCanonicalCloneAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (A : TwoIncomingTerminalCanonicalCloneAnalysis T hclaw) :
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
  exact T.lemma14_of_terminalStoppingAnalysis
    A.toTerminalStoppingAnalysis hclaw

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
