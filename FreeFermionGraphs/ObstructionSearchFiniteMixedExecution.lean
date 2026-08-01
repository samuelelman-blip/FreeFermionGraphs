import FreeFermionGraphs.ObstructionSearchFiniteMixedSnoc

/-!
# Inductively generated finite mixed-side executions

Definition 19 produces a nonempty finite sequence of literal path blocks.
The base block is constructed by `FiniteMixedSideSearchTrace.single`, and each
later block is appended by `FiniteMixedSideSearchTrace.snoc`.

This module records that construction as an inductive predicate and packages
the resulting search output with its generated trace.  The package cannot be
formed from an arbitrary supplied trace: its `generated` field must be built
from the literal one-block and append constructors.  No conclusion of
Lemma 11 or Lemma 14 is an input.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

namespace FiniteMixedSideSearchTrace

/-- A finite mixed trace generated from one literal Definition 19 block by
repeatedly appending literal successor blocks. -/
inductive IsLiteralExecution
    (originalHole : IndexedInducedHole G) :
    {S : SearchDeformation O Cprime} →
      FiniteMixedSideSearchTrace S originalHole → Prop
  | single
      (D : ConcretePathDeformation O Cprime)
      (side : DeformationSide)
      (F : (D.reorient side).FullDefinition19Lemma11AData)
      (hOriginal : Set.range D.initialHole.vertex =
        Set.range originalHole.vertex)
      (hRemoved : ∀ s : Fin D.deformation.stepCount,
        (D.deformation.step s).before.vertex
            (D.deformation.step s).removedIndex ∈
          Set.range originalHole.vertex)
      (hUnique : O.IsUniqueContainingPath
        (D.deformation.step D.firstIndex).introduced
        (Set.range D.path.vertex)) :
      IsLiteralExecution originalHole
        (FiniteMixedSideSearchTrace.single
          D side F hOriginal hRemoved hUnique)
  | snoc
      {S : SearchDeformation O Cprime}
      (X : FiniteMixedSideSearchTrace S originalHole)
      (hX : IsLiteralExecution originalHole X)
      (D : ConcretePathDeformation O Cprime)
      (side : DeformationSide)
      (F : (D.reorient side).FullDefinition19Lemma11AData)
      (hchain :
        Set.range (X.block X.lastBlockIndex).finalHole.vertex =
          Set.range D.initialHole.vertex)
      (hRemoved : ∀ s : Fin D.deformation.stepCount,
        (D.deformation.step s).before.vertex
            (D.deformation.step s).removedIndex ∈
          Set.range originalHole.vertex)
      (hFresh : ∀ i : Fin X.blockCount,
        Set.range (X.block i).path.vertex ≠ Set.range D.path.vertex)
      (hUnique : O.IsUniqueContainingPath
        (D.deformation.step D.firstIndex).introduced
        (Set.range D.path.vertex)) :
      IsLiteralExecution originalHole
        (X.snoc D side F hchain hRemoved hFresh hUnique)

end FiniteMixedSideSearchTrace

/-- A search output together with a finite trace whose complete provenance is
inductively generated from literal Definition 19 blocks. -/
structure LiteralFiniteMixedSideSearchExecution
    (originalHole : IndexedInducedHole G) where
  output : SearchDeformation O Cprime
  trace : FiniteMixedSideSearchTrace output originalHole
  generated : FiniteMixedSideSearchTrace.IsLiteralExecution originalHole trace

namespace LiteralFiniteMixedSideSearchExecution

/-- Start a literal execution with its first nonempty path block. -/
def single
    {originalHole : IndexedInducedHole G}
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (D.reorient side).FullDefinition19Lemma11AData)
    (hOriginal : Set.range D.initialHole.vertex =
      Set.range originalHole.vertex)
    (hRemoved : ∀ s : Fin D.deformation.stepCount,
      (D.deformation.step s).before.vertex
          (D.deformation.step s).removedIndex ∈
        Set.range originalHole.vertex)
    (hUnique : O.IsUniqueContainingPath
      (D.deformation.step D.firstIndex).introduced
      (Set.range D.path.vertex)) :
    LiteralFiniteMixedSideSearchExecution originalHole where
  output := D.singleBlockSearch side F
  trace := FiniteMixedSideSearchTrace.single
    D side F hOriginal hRemoved hUnique
  generated := FiniteMixedSideSearchTrace.IsLiteralExecution.single
    D side F hOriginal hRemoved hUnique

/-- Append one literal successor block to an inductively generated
execution. -/
def snoc
    {originalHole : IndexedInducedHole G}
    (X : LiteralFiniteMixedSideSearchExecution originalHole)
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (D.reorient side).FullDefinition19Lemma11AData)
    (hchain :
      Set.range (X.trace.block X.trace.lastBlockIndex).finalHole.vertex =
        Set.range D.initialHole.vertex)
    (hRemoved : ∀ s : Fin D.deformation.stepCount,
      (D.deformation.step s).before.vertex
          (D.deformation.step s).removedIndex ∈
        Set.range originalHole.vertex)
    (hFresh : ∀ i : Fin X.trace.blockCount,
      Set.range (X.trace.block i).path.vertex ≠ Set.range D.path.vertex)
    (hUnique : O.IsUniqueContainingPath
      (D.deformation.step D.firstIndex).introduced
      (Set.range D.path.vertex)) :
    LiteralFiniteMixedSideSearchExecution originalHole where
  output := X.trace.snocSearch D side F hchain
  trace := X.trace.snoc D side F hchain hRemoved hFresh hUnique
  generated := FiniteMixedSideSearchTrace.IsLiteralExecution.snoc
    X.trace X.generated D side F hchain hRemoved hFresh hUnique

@[simp] theorem single_blockCount
    {originalHole : IndexedInducedHole G}
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (D.reorient side).FullDefinition19Lemma11AData)
    (hOriginal : Set.range D.initialHole.vertex =
      Set.range originalHole.vertex)
    (hRemoved : ∀ s : Fin D.deformation.stepCount,
      (D.deformation.step s).before.vertex
          (D.deformation.step s).removedIndex ∈
        Set.range originalHole.vertex)
    (hUnique : O.IsUniqueContainingPath
      (D.deformation.step D.firstIndex).introduced
      (Set.range D.path.vertex)) :
    (single D side F hOriginal hRemoved hUnique).trace.blockCount = 1 :=
  rfl

@[simp] theorem snoc_blockCount
    {originalHole : IndexedInducedHole G}
    (X : LiteralFiniteMixedSideSearchExecution originalHole)
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (D.reorient side).FullDefinition19Lemma11AData)
    (hchain :
      Set.range (X.trace.block X.trace.lastBlockIndex).finalHole.vertex =
        Set.range D.initialHole.vertex)
    (hRemoved : ∀ s : Fin D.deformation.stepCount,
      (D.deformation.step s).before.vertex
          (D.deformation.step s).removedIndex ∈
        Set.range originalHole.vertex)
    (hFresh : ∀ i : Fin X.trace.blockCount,
      Set.range (X.trace.block i).path.vertex ≠ Set.range D.path.vertex)
    (hUnique : O.IsUniqueContainingPath
      (D.deformation.step D.firstIndex).introduced
      (Set.range D.path.vertex)) :
    (X.snoc D side F hchain hRemoved hFresh hUnique).trace.blockCount =
      X.trace.blockCount + 1 :=
  rfl

/-- The output paths of a literal execution are exactly its finite block
paths. -/
theorem output_path_iff
    {originalHole : IndexedInducedHole G}
    (X : LiteralFiniteMixedSideSearchExecution originalHole)
    (P : Set V) :
    P ∈ X.output.paths ↔
      ∃ i : Fin X.trace.blockCount,
        Set.range (X.trace.block i).path.vertex = P :=
  X.trace.output_path_iff P

/-- Exact Lemma 11(a.ii) is available for every output path of an
inductively generated literal execution. -/
theorem output_path_has_lemma11aii_exact
    {originalHole : IndexedInducedHole G}
    (X : LiteralFiniteMixedSideSearchExecution originalHole)
    {P : Set V} (hP : P ∈ X.output.paths)
    (hclaw : G.IsClawFree) :
    ∃ i : Fin X.trace.blockCount,
      Set.range (X.trace.block i).path.vertex = P ∧
        ∀ {s : Nat} {u : V},
          u ∈ (X.trace.block i).dependentAt s →
          u ∈ Cprime →
          (X.trace.block i).path.AnticommutesWith u →
            ((X.trace.block i).finalHole.externalDegree u = 4 ↔
              originalHole.externalDegree u = 3 ∧
                O.HasTypedClone .ad originalHole u) :=
  X.trace.output_path_has_lemma11aii_exact hP hclaw

end LiteralFiniteMixedSideSearchExecution

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
