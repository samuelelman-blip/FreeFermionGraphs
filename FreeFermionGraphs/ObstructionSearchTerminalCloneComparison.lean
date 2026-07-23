import FreeFermionGraphs.PaperFidelity

/-!
# Lemma 14(iv): comparing the two terminal clone centres

The manuscript compares the two holes obtained from the initialized searches,
`C_j^(m)` and `C_j'^(m')`.  In each hole the common obstruction target has
three neighbours and is a clone of a displayed centre.  The proof then splits
on equality of those two centre vertices.

This module makes the deformation stage explicit.  It defines the final hole
of an ordered initialized execution, represents each per-arc terminal clone in
that hole, and derives the same-centre/distinct-centre split by ordinary
vertex equality.  The branch split is therefore no longer an independent
pairwise certificate.

The branch consequences remain explicit obligations: equality of the centres
must yield the manuscript's same-clone terminal neighbourhood, while inequality
must yield the long distinct-clone propagation.  Constructing those facts from
the literal terminal histories remains the next boundary.
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

namespace OrderedOSExecution

/-- The manuscript hole after all path blocks of one initialized execution.

For an empty execution this is the initialized original hole.  For a nonempty
execution it is the final hole of the last ordered Definition 19 block.  This
is the Lean object corresponding to `C_j^(m)` in Lemma 14(iv). -/
noncomputable def manuscriptFinalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole) :
    IndexedInducedHole G :=
  if h : 0 < X.blockCount then
    (X.concreteBlock ⟨X.blockCount - 1, by omega⟩).finalHole
  else
    originalHole

/-- The terminal hole of an empty search is the initialized original hole. -/
@[simp] theorem manuscriptFinalHole_eq_original_of_blockCount_eq_zero
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hzero : X.blockCount = 0) :
    X.manuscriptFinalHole = originalHole := by
  simp [manuscriptFinalHole, hzero]

/-- The terminal hole of a nonempty search is the final hole of its last
ordered path block. -/
theorem manuscriptFinalHole_eq_last_of_pos
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount) :
    X.manuscriptFinalHole =
      (X.concreteBlock ⟨X.blockCount - 1, by omega⟩).finalHole := by
  simp [manuscriptFinalHole, hpos]

end OrderedOSExecution

/-- The target's clone in the final hole of one incoming initialized search.

This is the staged manuscript relation `j'' ≺_(C_j^(m)) v`.  The incoming arc
is a parameter rather than duplicated certificate data. -/
structure IncomingTerminalCloneWitness
    (T : I.InitializationTerminalCoreData)
    (source target : I.Node)
    (_incoming : I.graph.Arc source target) where
  cloneIndex :
    Fin (T.executionTrace.execution source).manuscriptFinalHole.card
  target_clone :
    ((T.executionTrace.execution source).manuscriptFinalHole).
      SingleVertexDeformation (target : V) cloneIndex

namespace IncomingTerminalCloneWitness

variable {T : I.InitializationTerminalCoreData}
  {source target : I.Node}
  {incoming : I.graph.Arc source target}

/-- The displayed centre vertex in the final hole `C_j^(m)`. -/
noncomputable def center
    (X : IncomingTerminalCloneWitness T source target incoming) : V :=
  (T.executionTrace.execution source).manuscriptFinalHole.vertex X.cloneIndex

/-- The target is adjacent to its displayed terminal clone centre. -/
theorem target_adj_center
    (X : IncomingTerminalCloneWitness T source target incoming) :
    G.Adj (target : V) X.center :=
  X.target_clone.adj_clone

/-- The displayed centre belongs to the correctly staged final hole. -/
theorem center_mem_finalHole
    (X : IncomingTerminalCloneWitness T source target incoming) :
    X.center ∈
      Set.range
        (T.executionTrace.execution source).manuscriptFinalHole.vertex :=
  ⟨X.cloneIndex, rfl⟩

end IncomingTerminalCloneWitness

/-- Pairwise terminal analysis with the manuscript's clone-centre comparison
made explicit.

The two per-arc clone witnesses are rooted in the two final execution holes.
The same/distinct branch is not supplied.  Instead, the analysis supplies the
appropriate manuscript continuation under equality or inequality of the two
actual centre vertices. -/
structure TwoIncomingTerminalCloneComparisonAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree) : Prop where
  terminalGeometry :
    ∀ ⦃source source' target : I.Node⦄
      (hne : source ≠ source')
      (incoming : I.graph.Arc source target)
      (incoming' : I.graph.Arc source' target),
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source target) ≠ (target : V) →
      (T.terminalPath target).obstructionEndpoint
          (T.currentSlot source' target) ≠ (target : V) →
        ∃ left : IncomingTerminalCloneWitness T source target incoming,
        ∃ right : IncomingTerminalCloneWitness T source' target incoming',
          (left.center = right.center →
            Nonempty
              ((T.terminalPath target).SameCloneTerminalNeighborhood
                (target : V))) ∧
          (left.center ≠ right.center →
            (Nonempty
                (DistinctClonePropagationFromDegreeOccurrence
                  T hclaw source target incoming) ∨
              Nonempty
                (DistinctClonePropagationFromDegreeOccurrence
                  T hclaw source' target incoming')))

namespace TwoIncomingTerminalCloneComparisonAnalysis

variable {T : I.InitializationTerminalCoreData}
  {hclaw : G.IsClawFree}

/-- Equality is decidable classically, so the two staged clone witnesses derive
exactly the same-clone/distinct-clone split used in the manuscript. -/
theorem toTerminalPredecessorDegreeAnalysis
    (A : TwoIncomingTerminalCloneComparisonAnalysis T hclaw) :
    TwoIncomingTerminalPredecessorDegreeAnalysis T hclaw := by
  classical
  refine { interiorGeometry := ?_ }
  intro source source' target hne incoming incoming' hsource hsource'
  obtain ⟨left, right, hsame, hdistinct⟩ :=
    A.terminalGeometry hne incoming incoming' hsource hsource'
  by_cases hcenter : left.center = right.center
  · exact
      TwoIncomingInteriorGeometryFromDegreeOccurrences.sameClone
        (hsame hcenter)
  · exact
      TwoIncomingInteriorGeometryFromDegreeOccurrences.distinctClone
        (hdistinct hcenter)

end TwoIncomingTerminalCloneComparisonAnalysis

namespace InitializationTerminalCoreData

/-- Conditional bridge to the exact paper-facing Lemma 14 statement after the
same/distinct split has been derived from the two final-hole clone centres. -/
theorem paperLemma14_of_terminalCloneComparisonAnalysis
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (A : TwoIncomingTerminalCloneComparisonAnalysis T hclaw) :
    PaperLemma14Conclusion I := by
  exact T.paperLemma14_of_terminalPredecessorDegreeAnalysis hclaw
    A.toTerminalPredecessorDegreeAnalysis

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
