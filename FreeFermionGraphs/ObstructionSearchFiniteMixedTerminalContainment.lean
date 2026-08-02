import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalOccurrence
import FreeFermionGraphs.ObstructionSearchTerminalPathComponentProvenance

/-!
# Terminal `C_b` carrier containment for finite mixed-side executions

The manuscript uses the inclusion

`P ∩ C_b ⊆ C_j^(m)`

for the terminal `bd` component `P`.  The key point is directional.  If an
initialized `C_b` vertex is absent from the final execution hole, a concrete
represented step removes it.  The oriented local Definition 19 geometry then
forces that step to be a `bd` block.  Its active path is therefore a `bd`
component containing the same vertex as the terminal `bd` component, so the
two components coincide.  This contradicts the stopping rule, which says the
terminal path was not appended to the execution.

All history quantifiers are bounded by the literal finite block count.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace PairingIndexedFamilyGeometry

variable {families : PairingType → FixedPairingPathFamily G}

/-- The two original-hole colour classes are disjoint in every pairing-indexed
presentation. -/
theorem ca_cb_disjoint_at
    (F : PairingIndexedFamilyGeometry families)
    (p : PairingType) :
    Disjoint (families p).Ca (families p).Cb := by
  rw [F.ca_eq p, F.cb_eq p]
  exact F.ca_cb_disjoint

end PairingIndexedFamilyGeometry

variable {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}
  {I : ObstructionSearchInitialization families Cprime}

namespace FiniteMixedSideOrderedOSExecution

/-- The removed vertex of an actual finite block lies in the original-hole
class selected by that block's side. -/
theorem removed_mem_selectedOriginalClass
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (q : Fin X.blockCount)
    (s : Fin (X.block q).deformation.stepCount) :
    match X.side q with
    | .ac =>
        (X.block q).deformation.step s |>.before.vertex
            ((X.block q).deformation.step s).removedIndex ∈
          (families (I.pairing source)).Ca
    | .bd =>
        (X.block q).deformation.step s |>.before.vertex
            ((X.block q).deformation.step s).removedIndex ∈
          (families (I.pairing source)).Cb := by
  have hremoved :=
    ((X.localData q).neighborhood.mechanical.stepGeometry s).removed_ca
  cases hside : X.side q with
  | ac =>
      simpa [hside, DeformationSide.family] using hremoved
  | bd =>
      simpa [hside, DeformationSide.family,
        FixedPairingPathFamily.swapSides] using hremoved

/-- Every finite ordered block belongs to the component family selected by its
side tag. -/
theorem path_mem_selectedSide
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (q : Fin X.blockCount) :
    match X.side q with
    | .ac => X.path q ∈ (families (I.pairing source)).acPaths
    | .bd => X.path q ∈ (families (I.pairing source)).bdPaths := by
  have hactive :
      Set.range
          (((X.block q).reorient (X.side q)).path.vertex) ∈
        ((X.side q).family (families (I.pairing source))).acPaths := by
    rw [← ((X.block q).reorient (X.side q)).activePath_eq
      ((X.block q).reorient (X.side q)).firstIndex]
    exact
      ((X.localData q).neighborhood.mechanical.stepGeometry
        ((X.block q).reorient (X.side q)).firstIndex).base.activePath_ac
  cases hside : X.side q with
  | ac =>
      simpa [FiniteMixedSideOrderedOSExecution.path, hside,
        DeformationSide.family] using hactive
  | bd =>
      simpa [FiniteMixedSideOrderedOSExecution.path, hside,
        DeformationSide.family, FixedPairingPathFamily.swapSides] using hactive

end FiniteMixedSideOrderedOSExecution

namespace ConcretePathDeformation.FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- A concrete removal represented in the context at block `i` belongs to an
actual block no later than `i`. -/
theorem exists_blockStep_le_of_contextAt_containsRemovedVertex
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) {x : V}
    (hx : (X.contextAt i).ContainsRemovedVertex x) :
    ∃ q : Fin X.blockCount,
      ∃ s : Fin (X.block q).deformation.stepCount,
        q.val ≤ i.val ∧
          x = (X.block q).deformation.step s |>.before.vertex
            ((X.block q).deformation.step s).removedIndex := by
  unfold contextAt at hx
  split at hx
  next hi =>
    change ∃ s : Fin (X.block i).deformation.stepCount,
      x = (X.block i).deformation.step s |>.before.vertex
        ((X.block i).deformation.step s).removedIndex at hx
    obtain ⟨s, hs⟩ := hx
    exact ⟨i, s, Nat.le_refl _, hs⟩
  next hi =>
    change
      (∃ r : Fin i.val,
        ∃ s : Fin (X.block (X.priorIndex i r)).deformation.stepCount,
          x = (X.block (X.priorIndex i r)).deformation.step s |>.before.vertex
            ((X.block (X.priorIndex i r)).deformation.step s).removedIndex) ∨
      ∃ s : Fin (X.block i).deformation.stepCount,
        x = (X.block i).deformation.step s |>.before.vertex
          ((X.block i).deformation.step s).removedIndex at hx
    rcases hx with hprior | hcurrent
    · obtain ⟨r, s, hs⟩ := hprior
      exact ⟨X.priorIndex i r, s, Nat.le_of_lt r.isLt, hs⟩
    · obtain ⟨s, hs⟩ := hcurrent
      exact ⟨i, s, Nat.le_refl _, hs⟩

end ConcretePathDeformation.FiniteMixedSideSearchTrace

namespace FiniteMixedSideOSExecution

/-- Lift bounded-context removal provenance through the literal empty/nonempty
execution split. -/
theorem exists_orderedBlockStep_le_of_contextAt_containsRemovedVertex
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    (i : Fin X.toOrdered.blockCount) {x : V}
    (hx : (X.contextAt i).ContainsRemovedVertex x) :
    ∃ q : Fin X.toOrdered.blockCount,
      ∃ s : Fin (X.toOrdered.block q).deformation.stepCount,
        q.val ≤ i.val ∧
          x = (X.toOrdered.block q).deformation.step s |>.before.vertex
            ((X.toOrdered.block q).deformation.step s).removedIndex := by
  cases X with
  | empty hrun =>
      exact Fin.elim0 i
  | nonempty data =>
      exact
        data.literal.trace.exists_blockStep_le_of_contextAt_containsRemovedVertex
          i hx

end FiniteMixedSideOSExecution

/-- Literal terminal-component provenance for the finite mixed-side core.
The terminal path is stored once per target, so its family is indexed by the
opposite of the target pairing. -/
structure FiniteMixedSideInitializationTerminalPathComponentData
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  terminalPath_mem_opposite_bd :
    ∀ ⦃source target : I.Node⦄,
      I.graph.Arc source target →
        Set.range (T.terminalPath target).vertex ∈
          (families ((I.pairing target).opposite)).bdPaths

namespace FiniteMixedSideInitializationTerminalPathComponentData

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- For an actual incoming finite search, the terminal path is a `bd`
component of the source pairing family. -/
theorem terminalPath_mem_source_bd
    (P : FiniteMixedSideInitializationTerminalPathComponentData T)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Set.range (T.terminalPath target).vertex ∈
      (families (I.pairing source)).bdPaths := by
  have hpair :
      (I.pairing target).opposite = I.pairing source := by
    have hopposite :=
      congrArg PairingType.opposite
        (T.obstructionOpposite hclaw incoming)
    simpa using hopposite
  simpa [hpair] using P.terminalPath_mem_opposite_bd incoming

end FiniteMixedSideInitializationTerminalPathComponentData

namespace InitializationFiniteMixedSideTerminalCoreData

/-- The finite version of the manuscript inclusion
`P ∩ C_b ⊆ C_j^(m)`.

The original-hole premise is written explicitly because `C_b` may overlap a
prime colour class away from the initialized hole. -/
theorem terminalCb_mem_manuscriptFinalHole
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (P : FiniteMixedSideInitializationTerminalPathComponentData T)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount)
    {x : V}
    (hxOriginal :
      x ∈ Set.range
        T.execution.toInitializationFiniteMixedSideOSExecutionData.originalHole.vertex)
    (hxCb : x ∈ (families (I.pairing source)).Cb)
    (hxTerminal : x ∈ Set.range (T.terminalPath target).vertex) :
    x ∈ Set.range
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole.vertex := by
  by_contra hxFinal
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  let X := Y.ordered source
  let last := X.lastBlockIndex hpos
  have hremovedContext :
      (Y.orderedContextAt source last).ContainsRemovedVertex x :=
    Y.containsRemovedVertex_of_mem_originalHole_of_not_mem_manuscriptFinalHole
      source hpos hxOriginal hxFinal
  obtain ⟨q, s, _hqle, hremoved⟩ :=
    (Y.execution source).
      exists_orderedBlockStep_le_of_contextAt_containsRemovedVertex
        last hremovedContext
  have hside : X.side q = .bd := by
    cases hs : X.side q with
    | ac =>
        have hxCa : x ∈ (families (I.pairing source)).Ca := by
          have hclass := X.removed_mem_selectedOriginalClass q s
          simpa [X, hs, hremoved] using hclass
        exact
          ((Set.disjoint_left.mp
            (T.pairingLabels.familyGeometry.ca_cb_disjoint_at
              (I.pairing source))) hxCa hxCb).elim
    | bd => exact hs
  have hpathBd : X.path q ∈ (families (I.pairing source)).bdPaths := by
    have h := X.path_mem_selectedSide q
    simpa [hside] using h
  have hxPath : x ∈ X.path q := by
    rw [hremoved]
    change
      (X.block q).deformation.step s |>.before.vertex
          ((X.block q).deformation.step s).removedIndex ∈
        Set.range (X.block q).path.vertex
    rw [← (X.block q).activePath_eq s]
    exact ((X.block q).deformation.step s).removed_mem_activePath
  have hterminalBd := P.terminalPath_mem_source_bd hclaw incoming
  have hpaths :
      Set.range (T.terminalPath target).vertex = X.path q :=
    (families (I.pairing source)).eq_of_mem_bdPaths
      hterminalBd hpathBd hxTerminal hxPath
  exact T.terminalPath_ne_executionPath incoming q hpaths

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
