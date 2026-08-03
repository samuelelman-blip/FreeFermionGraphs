import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalFlanks

/-!
# The first-block predecessor is the source-side terminal flank

In the unequal-centre branch the long propagation starts from the same-side
terminal-path vertex two positions toward the selected incoming endpoint.  The
selected positive execution encounters that vertex in its canonical first
Definition 19 block.  This module identifies the predecessor with that literal
flank and removes the free predecessor vertex from the remaining propagation
boundary.
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

namespace FiniteMixedSideTerminalTwoStepFlanks

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target : I.Node}

/-- The same-side flank lying toward one chosen terminal endpoint. -/
def towardEndpointIndex
    (F : FiniteMixedSideTerminalTwoStepFlanks T target)
    (slot : ObstructionSlot) : Fin (T.terminalPath target).card :=
  match slot with
  | .first => F.previousIndex
  | .last => F.nextIndex

/-- Vertex form of the source-side same-colour flank. -/
def towardEndpointVertex
    (F : FiniteMixedSideTerminalTwoStepFlanks T target)
    (slot : ObstructionSlot) : V :=
  (T.terminalPath target).vertex (F.towardEndpointIndex slot)

@[simp] theorem towardEndpointIndex_first
    (F : FiniteMixedSideTerminalTwoStepFlanks T target) :
    F.towardEndpointIndex .first = F.previousIndex := rfl

@[simp] theorem towardEndpointIndex_last
    (F : FiniteMixedSideTerminalTwoStepFlanks T target) :
    F.towardEndpointIndex .last = F.nextIndex := rfl

end FiniteMixedSideTerminalTwoStepFlanks

/-- Literal first-block occurrence of the source-side terminal flank.  The
predecessor vertex, block index, and first-block carrier equality are all
computed from the finite tether geometry. -/
structure FiniteMixedSideFirstBlockFlankOccurrence
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {target : I.Node}
    (F : FiniteMixedSideTerminalTwoStepFlanks T target)
    (source : I.Node)
    (incoming : I.graph.Arc source target) where
  positive :
    0 <
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount
  step : Nat
  mem_dependent :
    F.towardEndpointVertex (T.currentSlot source target) ∈
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block
          (InitializationFiniteMixedSideOSExecutionData.firstBlockIndex
            T.execution.toInitializationFiniteMixedSideOSExecutionData
            source positive)).dependentAt step
  finalDegree_three :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block
        (InitializationFiniteMixedSideOSExecutionData.firstBlockIndex
          T.execution.toInitializationFiniteMixedSideOSExecutionData
          source positive)).finalHole.externalDegree
      (F.towardEndpointVertex (T.currentSlot source target)) = 3

namespace FiniteMixedSideFirstBlockFlankOccurrence

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target source : I.Node}
  {incoming : I.graph.Arc source target}
  {F : FiniteMixedSideTerminalTwoStepFlanks T target}

/-- Forget only the path-derived name of the predecessor. -/
def toTetherOccurrence
    (W : FiniteMixedSideFirstBlockFlankOccurrence T F source incoming) :
    FiniteMixedSideFirstBlockTetherOccurrence T source
      (F.towardEndpointVertex (T.currentSlot source target)) where
  positive := W.positive
  step := W.step
  mem_dependent := W.mem_dependent
  finalDegree_three := W.finalDegree_three

/-- Direct conversion to the degree-only predecessor occurrence already used
by the finite distinct-clone contradiction. -/
def toDegreeOccurrence
    (W : FiniteMixedSideFirstBlockFlankOccurrence T F source incoming) :
    FiniteMixedSideFirstBlockPredecessorDegreeOccurrence T source
      (F.towardEndpointVertex (T.currentSlot source target)) :=
  W.toTetherOccurrence.toDegreeOccurrence

end FiniteMixedSideFirstBlockFlankOccurrence

/-- Distinct-clone propagation after identifying the predecessor with the
source-side terminal flank.  The remaining data are exactly the propagated
centre, original-hole neighbour, and their incidences produced by the long
path propagation. -/
structure FiniteMixedSideDistinctClonePropagationFromFlankOccurrence
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {target : I.Node}
    (F : FiniteMixedSideTerminalTwoStepFlanks T target)
    (source : I.Node)
    (incoming : I.graph.Arc source target) where
  predecessorOccurrence :
    Nonempty (FiniteMixedSideFirstBlockFlankOccurrence T F source incoming)
  center : V
  propagatedNeighbor : V
  adj_previous :
    G.Adj center
      (F.towardEndpointVertex (T.currentSlot source target))
  adj_propagatedNeighbor : G.Adj center propagatedNeighbor
  previous_ne_propagatedNeighbor :
    F.towardEndpointVertex (T.currentSlot source target) ≠ propagatedNeighbor
  propagatedNeighbor_ne_previousNeighbor :
    ∀ q : Fin
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.card,
      G.Adj
          (F.towardEndpointVertex (T.currentSlot source target))
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q) →
        propagatedNeighbor ≠
          T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex q
  propagatedNeighbor_mem_originalHole :
    propagatedNeighbor ∈ Set.range
      T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex
  cloneGeometry :
    FiniteMixedSideDistinctCloneGeometryWithoutPreviousPair
      T target center
        (F.towardEndpointVertex (T.currentSlot source target))
        propagatedNeighbor

namespace FiniteMixedSideDistinctClonePropagationFromFlankOccurrence

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target source : I.Node}
  {incoming : I.graph.Arc source target}
  {F : FiniteMixedSideTerminalTwoStepFlanks T target}

/-- Recover the previous degree-occurrence propagation interface. -/
noncomputable def toPropagationFromDegreeOccurrence
    (X : FiniteMixedSideDistinctClonePropagationFromFlankOccurrence
      T F source incoming) :
    FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
      T source target incoming := by
  let W : FiniteMixedSideFirstBlockFlankOccurrence T F source incoming :=
    Classical.choice X.predecessorOccurrence
  exact
    { previous := F.towardEndpointVertex (T.currentSlot source target)
      predecessorOccurrence := ⟨W.toDegreeOccurrence⟩
      center := X.center
      propagatedNeighbor := X.propagatedNeighbor
      adj_previous := X.adj_previous
      adj_propagatedNeighbor := X.adj_propagatedNeighbor
      previous_ne_propagatedNeighbor := X.previous_ne_propagatedNeighbor
      propagatedNeighbor_ne_previousNeighbor :=
        X.propagatedNeighbor_ne_previousNeighbor
      propagatedNeighbor_mem_originalHole :=
        X.propagatedNeighbor_mem_originalHole
      cloneGeometry := X.cloneGeometry }

end FiniteMixedSideDistinctClonePropagationFromFlankOccurrence

/-- Literal unequal-centre propagation data after the positive execution and
source-side terminal flank have been selected. -/
structure FiniteMixedSideDistinctCenterFlankPropagationData
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    (hclaw : G.IsClawFree) : Prop where
  propagate :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target)
      (hsource :
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source target) ≠ (target : V))
      (hsource' :
        (T.terminalPath target).obstructionEndpoint
            (T.currentSlot source' target) ≠ (target : V)),
      let C := D.toInteriorTerminalCloneData hclaw
      let left := C.witnessOfInterior incoming hsource
      let right := C.witnessOfInterior incoming' hsource'
      ∀ hcenter : left.center ≠ right.center,
        ∃ F : FiniteMixedSideTerminalTwoStepFlanks T target,
          match T.positiveDistinctSide_of_terminalClone_center_ne
              left right hcenter with
          | .left _ =>
              Nonempty
                (FiniteMixedSideDistinctClonePropagationFromFlankOccurrence
                  T F source incoming)
          | .right _ =>
              Nonempty
                (FiniteMixedSideDistinctClonePropagationFromFlankOccurrence
                  T F source' incoming')

namespace FiniteMixedSideDistinctCenterFlankPropagationData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {D : FiniteMixedSideInitializationTerminalTetherData T}
  {hclaw : G.IsClawFree}

/-- Flank-level propagation supplies the unequal-centre consequence required
by the tether integration theorem. -/
noncomputable def toDistinctCenterConsequences
    (A : FiniteMixedSideDistinctCenterFlankPropagationData T D hclaw) :
    D.DistinctCenterConsequences hclaw where
  propagate := by
    classical
    intro source source' target hne incoming incoming' hsource hsource'
    dsimp
    intro hcenter
    have hpropAll :=
      A.propagate hne incoming incoming' hsource hsource'
    dsimp at hpropAll
    obtain ⟨F, hprop⟩ := hpropAll hcenter
    cases hside : T.positiveDistinctSide_of_terminalClone_center_ne
        (D.toInteriorTerminalCloneData hclaw |>.witnessOfInterior incoming hsource)
        (D.toInteriorTerminalCloneData hclaw |>.witnessOfInterior incoming' hsource')
        hcenter with
    | left hpos =>
        have hleft : Nonempty
            (FiniteMixedSideDistinctClonePropagationFromFlankOccurrence
              T F source incoming) := by
          simpa [hside] using hprop
        obtain ⟨X⟩ := hleft
        exact Or.inl ⟨X.toPropagationFromDegreeOccurrence⟩
    | right hpos =>
        have hright : Nonempty
            (FiniteMixedSideDistinctClonePropagationFromFlankOccurrence
              T F source' incoming') := by
          simpa [hside] using hprop
        obtain ⟨X⟩ := hright
        exact Or.inr ⟨X.toPropagationFromDegreeOccurrence⟩

end FiniteMixedSideDistinctCenterFlankPropagationData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
