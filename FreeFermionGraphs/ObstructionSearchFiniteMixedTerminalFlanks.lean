import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalPositiveSide

/-!
# Two-step terminal flanks and the finite first block

The terminal component alternates between its two colour classes.  In the
interior two-incoming case the common target has even path index on an odd
path, so there are same-side vertices exactly two path positions before and
after it.  These are the manuscript vertices flanking `j''`.

For any positive finite execution, block zero is also canonically the first
literal trace block, so its initial carrier is the fixed initialized original
hole.  This removes the selected first-block index and carrier equality from
the remaining predecessor occurrence.
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

/-- The two same-side path vertices at distance two from the common terminal
target. -/
structure FiniteMixedSideTerminalTwoStepFlanks
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (target : I.Node) where
  targetIndex : Fin (T.terminalPath target).card
  target_eq : (T.terminalPath target).vertex targetIndex = (target : V)
  previousIndex : Fin (T.terminalPath target).card
  nextIndex : Fin (T.terminalPath target).card
  previous_gap : previousIndex.val + 2 = targetIndex.val
  next_gap : targetIndex.val + 2 = nextIndex.val

namespace FiniteMixedSideInitializationTerminalTetherData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- The literal alternating tether data determines the two same-side flanks in
the two-incoming interior branch. -/
theorem exists_twoStepFlanks
    (D : FiniteMixedSideInitializationTerminalTetherData T)
    (hclaw : G.IsClawFree)
    {source source' target : I.Node}
    (hne : source ≠ source')
    (incoming : I.graph.Arc source target)
    (incoming' : I.graph.Arc source' target)
    (hsource :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V))
    (hsource' :
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V)) :
    Nonempty (FiniteMixedSideTerminalTwoStepFlanks T target) := by
  let L := D.tether incoming
  have hend :=
    T.target_ne_both_terminalEndpoints_of_twoIncoming hclaw hne
      incoming incoming' hsource hsource'
  have hpositive : 0 < L.targetIndex.val := by
    by_contra hpos
    have hzero : L.targetIndex.val = 0 := by omega
    have hindex :
        (T.terminalPath target).obstructionEndpointIndex .first =
          L.targetIndex := by
      apply Fin.ext
      simp [IndexedInducedPath.obstructionEndpointIndex, hzero]
    apply hend.1
    rw [IndexedInducedPath.obstructionEndpoint, hindex, L.target_eq]
  have hupper : L.targetIndex.val + 1 < (T.terminalPath target).card := by
    by_contra hlt
    have hlast :
        L.targetIndex.val = (T.terminalPath target).card - 1 := by
      have hisLt := L.targetIndex.isLt
      omega
    have hindex :
        (T.terminalPath target).obstructionEndpointIndex .last =
          L.targetIndex := by
      apply Fin.ext
      simp [IndexedInducedPath.obstructionEndpointIndex, hlast]
    apply hend.2
    rw [IndexedInducedPath.obstructionEndpoint, hindex, L.target_eq]
  obtain ⟨a, ha⟩ := L.targetIndex_even
  obtain ⟨b, hb⟩ := L.pathCard_odd
  have hprevious : L.targetIndex.val - 2 < (T.terminalPath target).card := by
    omega
  have hnext : L.targetIndex.val + 2 < (T.terminalPath target).card := by
    omega
  let previousIndex : Fin (T.terminalPath target).card :=
    ⟨L.targetIndex.val - 2, hprevious⟩
  let nextIndex : Fin (T.terminalPath target).card :=
    ⟨L.targetIndex.val + 2, hnext⟩
  exact ⟨
    { targetIndex := L.targetIndex
      target_eq := L.target_eq
      previousIndex := previousIndex
      nextIndex := nextIndex
      previous_gap := by
        dsimp [previousIndex]
        omega
      next_gap := rfl }⟩

end FiniteMixedSideInitializationTerminalTetherData

namespace InitializationFiniteMixedSideOSExecutionData

/-- Canonical index of block zero in a positive literal finite execution. -/
def firstBlockIndex
    (Y : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (hpos : 0 < (Y.ordered source).blockCount) :
    Fin (Y.ordered source).blockCount :=
  ⟨0, hpos⟩

/-- Block zero of a positive ordered execution starts from the initialized
original hole. -/
theorem firstBlock_initial_eq_original
    (Y : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (hpos : 0 < (Y.ordered source).blockCount) :
    Set.range
        ((Y.ordered source).block (Y.firstBlockIndex source hpos)).initialHole.vertex =
      Set.range Y.originalHole.vertex := by
  cases hExec : Y.execution source with
  | empty hrun =>
      have hzero : (Y.ordered source).blockCount = 0 := by
        simp [InitializationFiniteMixedSideOSExecutionData.ordered,
          hExec, FiniteMixedSideOSExecution.toOrdered]
      omega
  | nonempty data =>
      simpa [InitializationFiniteMixedSideOSExecutionData.ordered,
        hExec, FiniteMixedSideOSExecution.toOrdered, firstBlockIndex] using
        data.literal.trace.originalHole_eq

end InitializationFiniteMixedSideOSExecutionData

/-- A predecessor occurrence in the canonical first finite block.  The block
index and its original-carrier equality are derived rather than stored. -/
structure FiniteMixedSideFirstBlockTetherOccurrence
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source : I.Node)
    (previous : V) where
  positive :
    0 <
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount
  step : Nat
  mem_dependent :
    previous ∈
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.
            firstBlockIndex source positive)).dependentAt step
  finalDegree_three :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.
          firstBlockIndex source positive)).finalHole.externalDegree previous = 3

namespace FiniteMixedSideFirstBlockTetherOccurrence

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source : I.Node} {previous : V}

/-- Recover the degree-only predecessor occurrence used by the existing finite
distinct-clone contradiction. -/
def toDegreeOccurrence
    (W : FiniteMixedSideFirstBlockTetherOccurrence T source previous) :
    FiniteMixedSideFirstBlockPredecessorDegreeOccurrence T source previous where
  blockIndex :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.
      firstBlockIndex source W.positive
  block_initial_eq_original :=
    T.execution.toInitializationFiniteMixedSideOSExecutionData.
      firstBlock_initial_eq_original source W.positive
  step := W.step
  mem_dependent := W.mem_dependent
  finalDegree_three := W.finalDegree_three

end FiniteMixedSideFirstBlockTetherOccurrence

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
