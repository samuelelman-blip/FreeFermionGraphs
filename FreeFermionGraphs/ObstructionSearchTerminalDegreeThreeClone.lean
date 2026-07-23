import FreeFermionGraphs.ObstructionSearchTerminalEmptyExecutionClone
import FreeFermionGraphs.Lemma11AThreeNeighborClone

/-!
# Lemma 14(iv): terminal degree three gives the final-hole clone

In the nonempty interior branch of Lemma 14(iv), the manuscript first proves
that the obstruction target lies outside the terminal execution hole and has
exactly three neighbours on that hole.  Lemma 7 then says that those neighbours
form a three-vertex path, so the target is a clone of the middle vertex.

This module identifies that graph-theoretic implication with the staged
`IncomingTerminalCloneWitness`.  It adds no terminal-history certificate: the
remaining search-specific obligation is exactly to derive the outside-hole and
degree-three facts from the positive-block tether history.
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

/-- An obstruction target outside the correctly staged manuscript final hole
with external degree three is a clone in that final hole. -/
theorem exists_terminalCloneWitness_of_finalHole_externalDegree_eq_three
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (houtside :
      (target : V) ∉ Set.range
        (T.executionTrace.execution source).manuscriptFinalHole.vertex)
    (hthree :
      (T.executionTrace.execution source).manuscriptFinalHole.externalDegree
        (target : V) = 3) :
    Nonempty (IncomingTerminalCloneWitness T source target incoming) := by
  obtain ⟨i, hi⟩ :=
    IndexedInducedHole.exists_singleVertexDeformation_of_externalDegree_eq_three
      (T.executionTrace.execution source).manuscriptFinalHole
      hclaw houtside hthree
  exact ⟨{ cloneIndex := i, target_clone := hi }⟩

/-- The empty execution is already discharged by the stopping branch.  Hence a
proof of the two manuscript terminal-geometry facts for every positive-block
execution suffices to construct the scoped final-hole clone witness. -/
theorem exists_terminalCloneWitness_of_positive_finalHole_geometry
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hgeometry :
      0 < (T.executionTrace.execution source).blockCount →
        (target : V) ∉ Set.range
            (T.executionTrace.execution source).manuscriptFinalHole.vertex ∧
          (T.executionTrace.execution source).manuscriptFinalHole.externalDegree
            (target : V) = 3) :
    Nonempty (IncomingTerminalCloneWitness T source target incoming) := by
  rcases T.terminalCloneWitness_or_blockCount_pos hclaw incoming with
    hwitness | hpos
  · exact hwitness
  · rcases hgeometry hpos with ⟨houtside, hthree⟩
    exact
      T.exists_terminalCloneWitness_of_finalHole_externalDegree_eq_three
        hclaw incoming houtside hthree

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
