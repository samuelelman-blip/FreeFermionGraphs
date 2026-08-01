import FreeFermionGraphs.ObstructionSearchFiniteMixedOSExecution

/-!
# Ordered finite mixed-side obstruction-search executions

The manuscript's least-common-path argument consumes a finite ordered block
family, including the empty family when an initialized `OS` call stops before
appending a path.  This module derives that uniform ordered interface from the
literal empty/nonempty execution split.

The ordered interface retains each concrete block, its selected side, and its
local Definition 19 data.  Output coverage, initializer incidence, and the
earlier-selection rule are derived from the literal execution rather than
accepted again as unrelated certificates.
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

/-- The finite ordered block data used by the least-common-path argument.
Unlike the legacy history interface, every block is indexed only below the
actual finite `blockCount`. -/
structure FiniteMixedSideOrderedOSExecution
    (I : ObstructionSearchInitialization families Cprime)
    (source : I.Node)
    (originalHole : IndexedInducedHole G) where
  blockCount : Nat
  block : Fin blockCount →
    ConcretePathDeformation (families (I.pairing source)) Cprime
  side : Fin blockCount → DeformationSide
  localData : ∀ i : Fin blockCount,
    ((block i).reorient (side i)).FullDefinition19Lemma11AData
  path_mem : ∀ i : Fin blockCount,
    Set.range (block i).path.vertex ∈ (I.output source).paths
  output_path : ∀ ⦃P : Set V⦄,
    P ∈ (I.output source).paths →
      ∃ i : Fin blockCount, Set.range (block i).path.vertex = P
  initializer_mem_path_iff : ∀ (i : Fin blockCount) (v : I.Node),
    (v : V) ∈ Set.range (block i).path.vertex ↔
      v = source ∧ i.val = 0
  earlierSelection :
    ∀ (i : Fin blockCount) (_ : 0 < i.val),
      ∃ (q : Fin blockCount) (s : Nat),
        q.val < i.val ∧
          ((block i).deformation.step (block i).firstIndex).introduced ∈
            (block q).dependentAt s ∧
          (block q).path.AnticommutesWith
            ((block i).deformation.step (block i).firstIndex).introduced

namespace FiniteMixedSideOrderedOSExecution

/-- Carrier of the `i`th ordered path. -/
def path
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) : Set V :=
  Set.range (X.block i).path.vertex

/-- First introduced vertex of the `i`th ordered block. -/
def entry
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) : V :=
  ((X.block i).deformation.step (X.block i).firstIndex).introduced

/-- Presentation of the stored output-membership field through `path`. -/
theorem path_mem'
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) :
    X.path i ∈ (I.output source).paths :=
  X.path_mem i

/-- Presentation of output coverage through `path`. -/
theorem output_path'
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    {P : Set V} (hP : P ∈ (I.output source).paths) :
    ∃ i : Fin X.blockCount, X.path i = P :=
  X.output_path hP

/-- Presentation of source incidence through `path`. -/
theorem initializer_mem_path_iff'
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) (v : I.Node) :
    (v : V) ∈ X.path i ↔ v = source ∧ i.val = 0 :=
  X.initializer_mem_path_iff i v

/-- Presentation of maximal-step earlier selection through `entry`. -/
theorem earlierSelection'
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOrderedOSExecution I source originalHole)
    (i : Fin X.blockCount) (hi : 0 < i.val) :
    ∃ (q : Fin X.blockCount) (s : Nat),
      q.val < i.val ∧
        X.entry i ∈ (X.block q).dependentAt s ∧
        (X.block q).path.AnticommutesWith (X.entry i) :=
  X.earlierSelection i hi

end FiniteMixedSideOrderedOSExecution

namespace FiniteMixedSideOSExecution

/-- Forget only the empty/nonempty case split while retaining the exact finite
ordered block family and every local invariant used by the least-common-path
argument. -/
def toOrdered
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole) :
    FiniteMixedSideOrderedOSExecution I source originalHole := by
  cases X with
  | empty hRun =>
      refine {
        blockCount := 0
        block := fun i => Fin.elim0 i
        side := fun i => Fin.elim0 i
        localData := fun i => Fin.elim0 i
        path_mem := fun i => Fin.elim0 i
        output_path := ?_
        initializer_mem_path_iff := fun i => Fin.elim0 i
        earlierSelection := fun i => Fin.elim0 i
      }
      intro P hP
      rcases hP with ⟨F, hSome, k, hk⟩
      have hFalse : False := by
        simpa [hRun] using hSome
      exact hFalse.elim
  | nonempty data =>
      refine {
        blockCount := data.blockCount
        block := data.block
        side := data.side
        localData := data.literal.trace.localData
        path_mem := ?_
        output_path := ?_
        initializer_mem_path_iff := ?_
        earlierSelection := ?_
      }
      · intro i
        exact data.path_mem i
      · intro P hP
        exact data.output_path hP
      · intro i v
        exact data.initializer_mem_path_iff i v
      · intro i hi
        exact data.earlierSelection i hi

end FiniteMixedSideOSExecution

namespace InitializationFiniteMixedSideOSExecutionData

/-- The finite ordered execution associated to initializer `source`. -/
def ordered
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node) :
    FiniteMixedSideOrderedOSExecution I source X.originalHole :=
  (X.execution source).toOrdered

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
