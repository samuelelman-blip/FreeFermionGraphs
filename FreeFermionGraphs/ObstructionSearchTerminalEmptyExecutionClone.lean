import FreeFermionGraphs.ObstructionSearchTerminalInteriorPathTriple
import FreeFermionGraphs.ObstructionSearchTerminalCloneFromStopping

/-!
# Lemma 14(iv): the final-hole clone for an empty initialized execution

The initialized obstruction search may return an empty deformation.  In that
case the manuscript terminal hole `C_j^(m)` is just the initialized original
hole.  The concrete stopping branch already supplies the target clone in that
original hole, so no tether propagation is needed.

This module discharges that boundary case and shows that any unresolved
final-hole clone witness must come from a nonempty execution.
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

/-- For an empty initialized execution, the stopping-branch clone in the
original hole is already the required clone in the manuscript final hole. -/
theorem exists_terminalCloneWitness_of_blockCount_eq_zero
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hzero : (T.executionTrace.execution source).blockCount = 0) :
    Nonempty (IncomingTerminalCloneWitness T source target incoming) := by
  obtain ⟨i, hi⟩ := T.exists_target_clone_of_incoming hclaw incoming
  refine ⟨{ cloneIndex := ?_, target_clone := ?_ }⟩
  · simpa [OrderedOSExecution.manuscriptFinalHole, hzero] using i
  · simpa [OrderedOSExecution.manuscriptFinalHole, hzero] using hi

/-- Every incoming arc either already has its final-hole clone witness by the
empty-execution argument, or its initialized execution is genuinely nonempty.
Thus the remaining tether proof may be scoped to positive block count. -/
theorem terminalCloneWitness_or_blockCount_pos
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target) :
    Nonempty (IncomingTerminalCloneWitness T source target incoming) ∨
      0 < (T.executionTrace.execution source).blockCount := by
  by_cases hzero : (T.executionTrace.execution source).blockCount = 0
  · exact Or.inl
      (T.exists_terminalCloneWitness_of_blockCount_eq_zero
        hclaw incoming hzero)
  · exact Or.inr (Nat.pos_of_ne_zero hzero)

/-- If every initialized execution is empty, the exact manuscript-scoped
final-hole clone interface follows entirely from the literal stopping
branches.  The interior premise is retained in the public interface but is not
needed in this special case. -/
theorem interiorTerminalCloneData_of_all_blockCount_eq_zero
    (T : I.InitializationTerminalCoreData)
    (hclaw : G.IsClawFree)
    (hzero : ∀ source : I.Node,
      (T.executionTrace.execution source).blockCount = 0) :
    InitializationInteriorTerminalCloneData T := by
  refine { exists_witness := ?_ }
  intro source target incoming _hinterior
  exact T.exists_terminalCloneWitness_of_blockCount_eq_zero
    hclaw incoming (hzero source)

end InitializationTerminalCoreData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
