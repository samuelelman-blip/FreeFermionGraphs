import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalCarrier

/-!
# Path occurrence provenance for finite mixed-side terminal executions

A missing initialized carrier vertex is removed by a concrete represented step,
so it lies on the corresponding active path.  This module turns that local fact
into an actual output-path occurrence for the bounded finite execution.

It also proves the literal stopping-rule fact that the terminal obstruction
path is not among the paths appended by the incoming search.  No component
colour or Lemma 14 conclusion is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

namespace FiniteMixedSideLemma11AContext

/-- A vertex occurs on the current path or one of the actual prior paths in the
bounded finite context. -/
def ContainsVertex
    (X : FiniteMixedSideLemma11AContext D originalHole) (x : V) : Prop :=
  match X with
  | .first _ _ _ => x ∈ Set.range D.path.vertex
  | .later H =>
      (∃ r : Fin H.priorCount,
        x ∈ Set.range (H.priorBlock r).path.vertex) ∨
      x ∈ Set.range D.path.vertex

/-- A concrete represented removal puts the removed vertex on one of the
represented active paths. -/
theorem containsVertex_of_containsRemovedVertex
    (X : FiniteMixedSideLemma11AContext D originalHole)
    {x : V}
    (hremoved : X.ContainsRemovedVertex x) :
    X.ContainsVertex x := by
  cases X with
  | first side current hinitial =>
      change ∃ i : Fin D.deformation.stepCount,
        x = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex at hremoved
      obtain ⟨i, rfl⟩ := hremoved
      change
        (D.deformation.step i).before.vertex
            (D.deformation.step i).removedIndex ∈
          Set.range D.path.vertex
      rw [← D.activePath_eq i]
      exact (D.deformation.step i).removed_mem_activePath
  | later H =>
      change
        (∃ r : Fin H.priorCount,
          ∃ i : Fin (H.priorBlock r).deformation.stepCount,
            x = ((H.priorBlock r).deformation.step i).before.vertex
              ((H.priorBlock r).deformation.step i).removedIndex) ∨
        ∃ i : Fin D.deformation.stepCount,
          x = (D.deformation.step i).before.vertex
            (D.deformation.step i).removedIndex at hremoved
      rcases hremoved with hprior | hcurrent
      · left
        obtain ⟨r, i, rfl⟩ := hprior
        refine ⟨r, ?_⟩
        rw [← (H.priorBlock r).activePath_eq i]
        exact ((H.priorBlock r).deformation.step i).removed_mem_activePath
      · right
        obtain ⟨i, rfl⟩ := hcurrent
        rw [← D.activePath_eq i]
        exact (D.deformation.step i).removed_mem_activePath

/-- A missing original-hole vertex occurs on one of the actual paths represented
by the bounded context. -/
theorem containsVertex_of_mem_originalHole_of_not_mem_currentFinalHole
    (X : FiniteMixedSideLemma11AContext D originalHole)
    {x : V}
    (hxOriginal : x ∈ Set.range originalHole.vertex)
    (hxNotFinal : x ∉ Set.range D.finalHole.vertex) :
    X.ContainsVertex x :=
  X.containsVertex_of_containsRemovedVertex
    (X.containsRemovedVertex_of_mem_originalHole_of_not_mem_currentFinalHole
      hxOriginal hxNotFinal)

end FiniteMixedSideLemma11AContext

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Every vertex occurrence in the finite context at block `i` comes from an
actual block no later than `i`. -/
theorem exists_block_le_of_contextAt_containsVertex
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) {x : V}
    (hx : (X.contextAt i).ContainsVertex x) :
    ∃ q : Fin X.blockCount,
      q.val ≤ i.val ∧ x ∈ Set.range (X.block q).path.vertex := by
  unfold contextAt at hx
  split at hx
  next hi =>
    refine ⟨i, Nat.le_refl _, ?_⟩
    simpa [FiniteMixedSideLemma11AContext.ContainsVertex] using hx
  next hi =>
    change
      (∃ r : Fin i.val,
        x ∈ Set.range
          (X.block (X.priorIndex i r)).path.vertex) ∨
      x ∈ Set.range (X.block i).path.vertex at hx
    rcases hx with ⟨r, hr⟩ | hcurrent
    · refine ⟨X.priorIndex i r, Nat.le_of_lt r.isLt, hr⟩
    · exact ⟨i, Nat.le_refl _, hcurrent⟩

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace FiniteMixedSideOSExecution

/-- A context occurrence at an actual ordered index is carried by an actual
ordered execution path.  The empty branch has no index. -/
theorem exists_orderedBlock_le_of_contextAt_containsVertex
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.toOrdered.blockCount) {x : V}
    (hx : (X.contextAt i).ContainsVertex x) :
    ∃ q : Fin X.toOrdered.blockCount,
      q.val ≤ i.val ∧ x ∈ X.toOrdered.path q := by
  cases X with
  | empty hrun =>
      exact Fin.elim0 i
  | nonempty data =>
      exact data.literal.trace.exists_block_le_of_contextAt_containsVertex
        i hx

/-- The stopping invariant excludes every other initializer from every actual
ordered path of the finite execution. -/
theorem otherSource_not_mem_orderedPath
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.toOrdered.blockCount) (v : I.Node)
    (hne : v ≠ source) :
    (v : V) ∉ X.toOrdered.path i := by
  cases X with
  | empty hrun =>
      exact Fin.elim0 i
  | nonempty data =>
      exact data.otherSource_not_mem_path i v hne

end FiniteMixedSideOSExecution

namespace InitializationFiniteMixedSideOSExecutionData

/-- A vertex occurrence in the last finite context yields an actual output path
of the same initialized search which contains that vertex. -/
theorem exists_output_path_of_orderedContext_containsVertex
    (Y : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (i : Fin (Y.ordered source).blockCount)
    {x : V}
    (hx : (Y.orderedContextAt source i).ContainsVertex x) :
    ∃ Q : Set V, Q ∈ (I.output source).paths ∧ x ∈ Q := by
  obtain ⟨q, _hqle, hxq⟩ :=
    (Y.execution source).exists_orderedBlock_le_of_contextAt_containsVertex
      i hx
  exact ⟨(Y.ordered source).path q,
    (Y.ordered source).path_mem' q, hxq⟩

/-- Consequently, an initialized original-hole vertex missing from the positive
finite terminal hole lies on some actual output path. -/
theorem exists_output_path_of_mem_originalHole_of_not_mem_manuscriptFinalHole
    (Y : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (hpos : 0 < (Y.ordered source).blockCount)
    {x : V}
    (hxOriginal : x ∈ Set.range Y.originalHole.vertex)
    (hxNotFinal : x ∉ Set.range (Y.ordered source).manuscriptFinalHole.vertex) :
    ∃ Q : Set V, Q ∈ (I.output source).paths ∧ x ∈ Q := by
  apply Y.exists_output_path_of_orderedContext_containsVertex
    source ((Y.ordered source).lastBlockIndex hpos)
  have hxNotLast :
      x ∉ Set.range
        ((Y.ordered source).block
          ((Y.ordered source).lastBlockIndex hpos)).finalHole.vertex := by
    intro hx
    apply hxNotFinal
    rw [(Y.ordered source).manuscriptFinalHole_eq_lastBlockFinalHole hpos]
    exact hx
  exact ConcretePathDeformation.FiniteMixedSideLemma11AContext.
    containsVertex_of_mem_originalHole_of_not_mem_currentFinalHole
      (Y.orderedContextAt source
        ((Y.ordered source).lastBlockIndex hpos))
      hxOriginal hxNotLast

end InitializationFiniteMixedSideOSExecutionData

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Nearest-target selection places every obstruction target on its terminal
path. -/
theorem target_mem_terminalPath
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    (target : V) ∈ Set.range (T.terminalPath target).vertex := by
  obtain ⟨q, htarget, _hnearest⟩ :=
    T.nearestTarget.obstruction_nearest incoming
  exact ⟨q, htarget⟩

/-- The stopping invariant excludes the obstruction target from every actual
execution path of its incoming search. -/
theorem target_not_mem_executionPath
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (i : Fin
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount) :
    (target : V) ∉
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).path i := by
  exact
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.execution
      source).otherSource_not_mem_orderedPath i target
        (T.nearestTarget.target_ne_source incoming)

/-- The terminal obstruction path differs from every path actually appended by
the incoming finite search. -/
theorem terminalPath_ne_executionPath
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (i : Fin
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount) :
    Set.range (T.terminalPath target).vertex ≠
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).path i := by
  intro hEq
  apply T.target_not_mem_executionPath incoming i
  rw [← hEq]
  exact T.target_mem_terminalPath incoming

/-- The terminal obstruction path is not one of the finite output paths of the
search which stopped on it. -/
theorem terminalPath_not_mem_outputPaths
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Set.range (T.terminalPath target).vertex ∉
      (I.output source).paths := by
  intro hmem
  obtain ⟨i, hi⟩ :=
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).output_path' hmem
  exact T.terminalPath_ne_executionPath incoming i hi.symm

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
