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

namespace FiniteMixedSideOSExecution

/-- Every actual index of one possibly empty execution carries the context of
the corresponding literal trace block. -/
def contextAt
    {source : I.Node} {originalHole : IndexedInducedHole G} :
    (X : FiniteMixedSideOSExecution I source originalHole) →
    (i : Fin X.toOrdered.blockCount) →
      ConcretePathDeformation.FiniteMixedSideLemma11AContext
        (X.toOrdered.block i) originalHole
  | .empty _, i => Fin.elim0 i
  | .nonempty data, i => data.literal.trace.contextAt i

end FiniteMixedSideOSExecution

namespace InitializationFiniteMixedSideOSExecutionData

/-- Every actual ordered block index recovers its literal zero-or-positive
finite history context.  The empty execution branch has no such index. -/
def orderedContextAt
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (i : Fin (X.ordered source).blockCount) :
    ConcretePathDeformation.FiniteMixedSideLemma11AContext
      ((X.ordered source).block i) X.originalHole :=
  (X.execution source).contextAt i

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph