import FreeFermionGraphs.ObstructionSearchFiniteMixedCrossCorollary11

/-!
# Finite contexts for initialized ordered execution indices

The uniform ordered interface includes an empty execution as a zero-block
family.  Consequently every actual ordered index comes from the nonempty
literal trace and has the canonical finite context constructed there.  This
module exposes that dependent bridge without adding context data to the
ordered execution structure itself.
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

namespace InitializationFiniteMixedSideOSExecutionData

/-- Every actual ordered block index recovers its literal zero-or-positive
finite history context.  The empty execution branch has no such index. -/
def orderedContextAt
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (i : Fin (X.ordered source).blockCount) :
    ConcretePathDeformation.FiniteMixedSideLemma11AContext
      ((X.ordered source).block i) X.originalHole := by
  unfold ordered
  cases h : X.execution source with
  | empty hRun =>
      have hi : False := by
        have hiLt := i.isLt
        simpa [h, FiniteMixedSideOSExecution.toOrdered] using hiLt
      exact hi.elim
  | nonempty data =>
      simpa [h, FiniteMixedSideOSExecution.toOrdered] using
        data.literal.trace.contextAt i

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
