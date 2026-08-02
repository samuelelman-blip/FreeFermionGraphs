import FreeFermionGraphs.PaperFidelity
import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalPredecessorAnticommutation

/-!
# Comparing finite terminal clone centres

The manuscript compares the two holes obtained after the two initialized
obstruction searches, `C_j^(m)` and `C_j'^(m')`.  In each final execution hole
the common obstruction target is a clone of a displayed centre, and the proof
splits on equality of those two centre vertices.

This module makes that deformation stage explicit for literal finite
mixed-side executions.  The same-clone/distinct-clone split is derived by
ordinary equality of the two staged centre vertices rather than supplied as a
terminal certificate.
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

namespace FiniteMixedSideOrderedOSExecution

/-- The manuscript hole after all blocks of one literal finite mixed-side
execution.  Empty executions retain the initialized original hole; positive
executions use the final hole of the last concrete block. -/
noncomputable def manuscriptFinalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole) :
    IndexedInducedHole G :=
  if h : 0 < X.blockCount then
    (X.block ⟨X.blockCount - 1, by omega⟩).finalHole
  else
    originalHole

/-- The final hole of an empty finite execution is the initialized original
hole. -/
@[simp] theorem manuscriptFinalHole_eq_original_of_blockCount_eq_zero
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (hzero : X.blockCount = 0) :
    X.manuscriptFinalHole = originalHole := by
  simp [manuscriptFinalHole, hzero]

/-- The final hole of a positive finite execution is the last block's final
hole. -/
theorem manuscriptFinalHole_eq_last_of_pos
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount) :
    X.manuscriptFinalHole =
      (X.block ⟨X.blockCount - 1, by omega⟩).finalHole := by
  simp [manuscriptFinalHole, hpos]

end FiniteMixedSideOrderedOSExecution

/-- The common target's clone in the final hole of one incoming literal finite
execution.  This is the staged manuscript relation
`j'' ≺_(C_j^(m)) v`. -/
structure FiniteMixedSideIncomingTerminalCloneWitness
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (source target : I.Node)
    (_incoming : I.graph.Arc source target) where
  cloneIndex : Fin
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.card)
  target_clone :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole).SingleVertexDeformation
        (target : V) cloneIndex

namespace FiniteMixedSideIncomingTerminalCloneWitness

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- The displayed centre in the correctly staged final execution hole. -/
noncomputable def center
    (X : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming) : V :=
  (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
    source).manuscriptFinalHole.vertex X.cloneIndex

/-- The obstruction target is adjacent to its displayed final-hole clone
centre. -/
theorem target_adj_center
    (X : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming) :
    G.Adj (target : V) X.center :=
  X.target_clone.adj_clone

/-- The displayed centre belongs to the final execution hole in which its
clone relation is stated. -/
theorem center_mem_finalHole
    (X : FiniteMixedSideIncomingTerminalCloneWitness
      T source target incoming) :
    X.center ∈ Set.range
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).manuscriptFinalHole.vertex :=
  ⟨X.cloneIndex, rfl⟩

end FiniteMixedSideIncomingTerminalCloneWitness

/-- Pairwise finite terminal analysis with the manuscript's final-hole clone
comparison explicit.  Equality and inequality of the two actual centre
vertices imply the corresponding manuscript continuation; the branch split
itself is not stored. -/
structure FiniteMixedSideTwoIncomingTerminalCloneComparisonAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Prop where
  terminalGeometry :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target),
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        ∃ left : FiniteMixedSideIncomingTerminalCloneWitness
            T source target incoming,
        ∃ right : FiniteMixedSideIncomingTerminalCloneWitness
            T source' target incoming',
          (left.center = right.center →
            Nonempty
              ((T.terminalPath target).SameCloneTerminalNeighborhood
                (target : V))) ∧
          (left.center ≠ right.center →
            (Nonempty
                (FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
                  T source target incoming) ∨
              Nonempty
                (FiniteMixedSideDistinctClonePropagationFromDegreeOccurrence
                  T source' target incoming')))

namespace FiniteMixedSideTwoIncomingTerminalCloneComparisonAnalysis

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- Classical equality of the two staged centre vertices derives exactly the
same-clone/distinct-clone split used by the manuscript. -/
noncomputable def toTerminalPredecessorDegreeAnalysis
    (A : FiniteMixedSideTwoIncomingTerminalCloneComparisonAnalysis T) :
    FiniteMixedSideTwoIncomingTerminalPredecessorDegreeAnalysis T where
  interiorGeometry := by
    classical
    intro source source' target hne incoming incoming' hsource hsource'
    obtain ⟨left, right, hsame, hdistinct⟩ :=
      A.terminalGeometry hne incoming incoming' hsource hsource'
    by_cases hcenter : left.center = right.center
    · exact
        FiniteMixedSideTwoIncomingInteriorGeometryFromDegreeOccurrences.sameClone
          (hsame hcenter)
    · exact
        FiniteMixedSideTwoIncomingInteriorGeometryFromDegreeOccurrences.distinctClone
          (hdistinct hcenter)

end FiniteMixedSideTwoIncomingTerminalCloneComparisonAnalysis

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Conditional bridge from the finite staged clone comparison to the exact
paper-facing four-part conclusion of Lemma 14. -/
theorem paperLemma14_of_terminalCloneComparisonAnalysis
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (A : FiniteMixedSideTwoIncomingTerminalCloneComparisonAnalysis T)
    (hclaw : G.IsClawFree) :
    PaperLemma14Conclusion I := by
  simpa only [PaperLemma14Conclusion] using
    T.lemma14_of_terminalPredecessorDegreeAnalysis
      A.toTerminalPredecessorDegreeAnalysis hclaw

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
