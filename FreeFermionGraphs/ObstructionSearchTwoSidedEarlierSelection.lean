import FreeFermionGraphs.ObstructionSearchTwoSidedExecution

/-!
# Two-sided maximal-step earlier selection

The manuscript `OS` update selects the first introduced vertex of every later
path block from a dependent set of a strictly earlier block, with
anticommutation against that earlier path.  This module records that literal
maximal-`L_{r,s}` execution invariant over the side-correct block witnesses.

No first-common-path equality, disjointness, terminal-hole geometry, or Lemma 14
conclusion is stored.
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

/-- A complete local initialized `OS` execution over the paper-faithful
side-correct path history.

`earlierSelection` is the exact update rule used in the ordered-search proof:
for every noninitial block, its first introduced vertex is selected from a
dependent set of a strictly earlier block and anticommutes with that block's
path. -/
structure TwoSidedOrderedOSExecution
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node)
    (originalHole : IndexedInducedHole G) where
  ordered : TwoSidedOrderedPathExecution I source originalHole
  entry : Fin ordered.blockCount → V
  entry_is_firstIntroduced :
    ∀ i : Fin ordered.blockCount,
      entry i =
        (((ordered.blockWitness i).block.deformation.step
          (ordered.blockWitness i).block.firstIndex).introduced)
  earlierSelection :
    ∀ (i : Fin ordered.blockCount) (_ : 0 < i.val),
      ∃ (q : Fin ordered.blockCount) (s : Nat),
        q.val < i.val ∧
          entry i ∈ ((ordered.blockWitness q).block.dependentAt s) ∧
          ((ordered.blockWitness q).block.path).AnticommutesWith
            (entry i)

namespace TwoSidedOrderedOSExecution

/-- The underlying path-block count. -/
abbrev blockCount
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedOSExecution I source originalHole) : Nat :=
  X.ordered.blockCount

/-- The indexed path carrier. -/
abbrev path
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) : Set V :=
  X.ordered.path i

/-- Every indexed path is an output path of this initialized search. -/
theorem path_mem
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) :
    X.path i ∈ (I.output source).paths :=
  X.ordered.path_mem i

/-- Every output path occurs at an indexed block. -/
theorem output_path
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedOSExecution I source originalHole)
    {P : Set V} (hP : P ∈ (I.output source).paths) :
    ∃ i : Fin X.blockCount, X.path i = P :=
  X.ordered.output_path hP

/-- Initializer incidence remains the exact first-block statement. -/
theorem initializer_mem_path_iff
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : TwoSidedOrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) (v : I.Node) :
    (v : V) ∈ X.path i ↔ v = source ∧ i.val = 0 :=
  X.ordered.initializer_mem_path_iff i v

end TwoSidedOrderedOSExecution

namespace OrderedOSExecution

/-- The old one-sided execution embeds into the complete side-correct local
execution as the `.ac` compatibility case.  This does not construct manuscript
`.bd` blocks; it only verifies that the new interface preserves the existing
execution data. -/
def toTwoSidedOrderedOSExecution
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole) :
    TwoSidedOrderedOSExecution I source originalHole where
  ordered := X.toTwoSidedOrderedPathExecution
  entry := X.entry
  entry_is_firstIntroduced := by
    intro i
    rfl
  earlierSelection := by
    intro i hi
    obtain ⟨q, s, hqi, hdep, hanti⟩ := X.earlierSelection i hi
    refine ⟨q, s, hqi, ?_, ?_⟩
    · simpa [TwoSidedOrderedPathExecution.blockWitness,
        OrderedOSExecution.toTwoSidedOrderedPathExecution,
        SearchHistoryData.toTwoSided,
        SearchPathHistoryWitness.toTwoSided] using hdep
    · simpa [TwoSidedOrderedPathExecution.blockWitness,
        OrderedOSExecution.toTwoSidedOrderedPathExecution,
        SearchHistoryData.toTwoSided,
        SearchPathHistoryWitness.toTwoSided] using hanti

end OrderedOSExecution

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
