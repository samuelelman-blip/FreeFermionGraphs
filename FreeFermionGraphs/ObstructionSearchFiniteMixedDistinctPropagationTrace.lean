import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalFlankOccurrence

/-!
# Literal finite trace for the unequal-centre propagation

The long final paragraph of Lemma 14(iv) propagates an original-hole vertex
through a finite sequence of actual path components.  At each hop the carried
original-hole vertex belongs to the selected execution path.  The propagation
maintains three coordinate-level avoidance invariants: the carried index is
not a neighbour index of the source-side predecessor, is not the stopping-
branch clone index, and is not cyclically adjacent to that clone index.

This module derives all uniform inequalities required by the existing final
claw argument from those bounded trace invariants.  The trace does not contain
a claw, an endpoint conclusion, or any part of the Lemma 14 conclusion.
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

/-- A bounded path-by-path propagation on one selected positive execution.
The predecessor is the source-side two-step terminal flank, while the target's
original-hole clone index is fixed by the literal stopping branch. -/
structure FiniteMixedSideDistinctPropagationTrace
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {target : I.Node}
    (F : FiniteMixedSideTerminalTwoStepFlanks T target)
    (source : I.Node)
    (incoming : I.graph.Arc source target) where
  predecessorOccurrence :
    Nonempty (FiniteMixedSideFirstBlockFlankOccurrence T F source incoming)
  previous_outside_originalHole :
    F.towardEndpointVertex (T.currentSlot source target) ∉
      Set.range
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  center : V
  hopCount : Nat
  carriedIndex : Fin (hopCount + 1) → Fin
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card
  hopBlock : Fin hopCount → Fin
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).blockCount
  carried_mem_hopPath : ∀ k : Fin hopCount,
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        (carriedIndex (Fin.castSucc k)) ∈
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).path (hopBlock k)
  next_mem_hopPath : ∀ k : Fin hopCount,
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        (carriedIndex (Fin.succ k)) ∈
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).path (hopBlock k)
  carried_avoidance : ∀ k : Fin (hopCount + 1),
    carriedIndex k ∉
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole).
          neighborIndexSet
            (F.towardEndpointVertex (T.currentSlot source target)) ∧
      carriedIndex k ≠ T.targetCloneIndexOfIncoming hclaw incoming ∧
      ¬CyclicAdjacent
        (T.targetCloneIndexOfIncoming hclaw incoming) (carriedIndex k)
  clone_avoids_previousNeighbors :
    T.targetCloneIndexOfIncoming hclaw incoming ∉
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole).
        neighborIndexSet
          (F.towardEndpointVertex (T.currentSlot source target))
  adj_previous :
    G.Adj center
      (F.towardEndpointVertex (T.currentSlot source target))
  adj_finalCarried :
    G.Adj center
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        (carriedIndex ⟨hopCount, by omega⟩))
  adj_stoppingCloneCenter :
    G.Adj center
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
        (T.targetCloneIndexOfIncoming hclaw incoming))

namespace FiniteMixedSideDistinctPropagationTrace

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {hclaw : G.IsClawFree}
  {target source : I.Node}
  {incoming : I.graph.Arc source target}
  {F : FiniteMixedSideTerminalTwoStepFlanks T target}

/-- Last carried original-hole index. -/
def finalIndex
    (X : FiniteMixedSideDistinctPropagationTrace
      T hclaw F source incoming) : Fin (X.hopCount + 1) :=
  ⟨X.hopCount, by omega⟩

/-- Last carried original-hole vertex. -/
def finalVertex
    (X : FiniteMixedSideDistinctPropagationTrace
      T hclaw F source incoming) : V :=
  T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
    (X.carriedIndex X.finalIndex)

/-- The predecessor differs from the final carried vertex because the former is
outside and the latter is on the initialized original hole. -/
theorem previous_ne_finalVertex
    (X : FiniteMixedSideDistinctPropagationTrace
      T hclaw F source incoming) :
    F.towardEndpointVertex (T.currentSlot source target) ≠ X.finalVertex := by
  intro hEq
  apply X.previous_outside_originalHole
  exact ⟨X.carriedIndex X.finalIndex, hEq.symm⟩

/-- The final carried vertex is different from every original-hole neighbour
of the predecessor. -/
theorem finalVertex_ne_previousNeighbor
    (X : FiniteMixedSideDistinctPropagationTrace
      T hclaw F source incoming)
    (q : Fin
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card)
    (hAdj : G.Adj
      (F.towardEndpointVertex (T.currentSlot source target))
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q)) :
    X.finalVertex ≠
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q := by
  intro hEq
  have hIndex : X.carriedIndex X.finalIndex = q :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.injective hEq
  apply (X.carried_avoidance X.finalIndex).1
  rw [hIndex]
  exact hAdj

/-- Recover the flank-level propagation package.  All noncollision conditions
are consequences of the trace's index invariants and clone-centre uniqueness. -/
noncomputable def toPropagationFromFlankOccurrence
    (X : FiniteMixedSideDistinctPropagationTrace
      T hclaw F source incoming) :
    FiniteMixedSideDistinctClonePropagationFromFlankOccurrence
      T F source incoming := by
  let C :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole
  let canonical := T.targetCloneIndexOfIncoming hclaw incoming
  have hcanonical : C.SingleVertexDeformation (target : V) canonical := by
    simpa [C, canonical] using
      T.targetCloneIndexOfIncoming_spec hclaw incoming
  exact
    { predecessorOccurrence := X.predecessorOccurrence
      center := X.center
      propagatedNeighbor := X.finalVertex
      adj_previous := X.adj_previous
      adj_propagatedNeighbor := X.adj_finalCarried
      previous_ne_propagatedNeighbor := X.previous_ne_finalVertex
      propagatedNeighbor_ne_previousNeighbor :=
        X.finalVertex_ne_previousNeighbor
      propagatedNeighbor_mem_originalHole :=
        ⟨X.carriedIndex X.finalIndex, rfl⟩
      cloneGeometry :=
        { adj_cloneCenter := by
            intro cloneIndex hclone
            have hEq : cloneIndex = canonical :=
              hclone.center_eq hcanonical
            subst cloneIndex
            exact X.adj_stoppingCloneCenter
          previous_ne_cloneCenter := by
            intro cloneIndex hclone hEq
            apply X.previous_outside_originalHole
            exact ⟨cloneIndex, hEq.symm⟩
          propagatedNeighbor_ne_cloneCenter := by
            intro cloneIndex hclone hEq
            have hCloneIndex : cloneIndex = canonical :=
              hclone.center_eq hcanonical
            have hCarried : X.carriedIndex X.finalIndex = cloneIndex :=
              C.injective hEq
            apply (X.carried_avoidance X.finalIndex).2.1
            rw [hCarried, hCloneIndex]
          cloneCenter_ne_previousNeighbor := by
            intro cloneIndex q hclone hAdj hEq
            have hCloneIndex : cloneIndex = canonical :=
              hclone.center_eq hcanonical
            have hIndex : cloneIndex = q := C.injective hEq
            apply X.clone_avoids_previousNeighbors
            rw [← hCloneIndex, hIndex]
            exact hAdj
          propagatedNeighbor_ne_cycleNeighbor := by
            intro cloneIndex q hclone hAdj hEq
            have hCloneIndex : cloneIndex = canonical :=
              hclone.center_eq hcanonical
            have hCarried : X.carriedIndex X.finalIndex = q :=
              C.injective hEq
            have hCyclic : CyclicAdjacent canonical q := by
              rw [← hCloneIndex]
              exact (C.adj_iff cloneIndex q).1 hAdj
            apply (X.carried_avoidance X.finalIndex).2.2
            rw [hCarried]
            exact hCyclic } }

end FiniteMixedSideDistinctPropagationTrace

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
