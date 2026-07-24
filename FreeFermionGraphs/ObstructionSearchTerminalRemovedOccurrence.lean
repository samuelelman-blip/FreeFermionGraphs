import FreeFermionGraphs.ObstructionSearchTerminalComponentOccurrence

/-!
# Lemma 14(iv): a missing carrier vertex is removed by a concrete step

The corrected carrier argument first needs an introduced/removed orientation
statement.  Merely knowing that an original-hole vertex occurs on an executed
path is insufficient, because Corollary 9 permits one `ac` and one `bd` path to
meet at an overlap vertex.

This module proves the orientation fact supplied by the deformation carriers:
if a vertex starts on the original hole and is absent from the current final
hole, then it equals the removed vertex of some represented concrete step.  It
does not yet classify that step as an `ac` or `bd` block.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A vertex present before a path block and absent after it must be removed at
one of the block's concrete deformation steps. -/
theorem exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
    (D : ConcretePathDeformation O Cprime)
    {x : V}
    (hxInitial : x ∈ Set.range D.initialHole.vertex)
    (hxNotFinal : x ∉ Set.range D.finalHole.vertex) :
    ∃ i : Fin D.deformation.stepCount,
      x = (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex := by
  by_contra hnone
  have hne : ∀ i : Fin D.deformation.stepCount,
      x ≠ (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex := by
    intro i hEq
    apply hnone
    exact ⟨i, hEq⟩
  have hafter : ∀ (n : Nat) (hn : n < D.deformation.stepCount),
      x ∈ Set.range (D.deformation.step ⟨n, hn⟩).after.vertex := by
    intro n
    induction n with
    | zero =>
        intro hn
        let current : Fin D.deformation.stepCount := ⟨0, hn⟩
        have hbefore :
            x ∈ Set.range (D.deformation.step current).before.vertex := by
          simpa [current, initialHole, firstIndex] using hxInitial
        simpa [current] using
          (D.deformation.step current).mem_after_of_mem_before_of_ne_removed
            hbefore (hne current)
    | succ n ih =>
        intro hn
        have hnPrevious : n < D.deformation.stepCount := by omega
        let previous : Fin D.deformation.stepCount := ⟨n, hnPrevious⟩
        let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
        have hprevious :
            x ∈ Set.range (D.deformation.step previous).after.vertex := by
          simpa [previous] using ih hnPrevious
        have hchain :
            Set.range (D.deformation.step previous).after.vertex =
              Set.range (D.deformation.step current).before.vertex :=
          D.deformation.carrier_chain (i := previous) (j := current) (by
            simp [previous, current])
        have hbefore :
            x ∈ Set.range (D.deformation.step current).before.vertex := by
          rw [← hchain]
          exact hprevious
        simpa [current] using
          (D.deformation.step current).mem_after_of_mem_before_of_ne_removed
            hbefore (hne current)
  have hlast : D.deformation.stepCount - 1 < D.deformation.stepCount := by
    have hpos := D.nonempty
    omega
  have hfinal := hafter (D.deformation.stepCount - 1) hlast
  apply hxNotFinal
  simpa [finalHole, lastIndex] using hfinal

namespace PathBlockHistory

/-- If a vertex is on the first initial hole but absent from the final hole of
block `n`, one of the first `n+1` blocks removes it at a concrete step. -/
theorem exists_removedStep_through_of_mem_firstInitial_of_not_mem_finalHole
    (H : PathBlockHistory (O := O) (Cprime := Cprime))
    {x : V} (n : Nat)
    (hxInitial : x ∈ Set.range (H.block 0).initialHole.vertex)
    (hxNotFinal : x ∉ Set.range (H.block n).finalHole.vertex) :
    ∃ r : Nat, r ≤ n ∧
      ∃ i : Fin (H.block r).deformation.stepCount,
        x = ((H.block r).deformation.step i).before.vertex
          ((H.block r).deformation.step i).removedIndex := by
  induction n with
  | zero =>
      rcases (H.block 0).exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
          hxInitial hxNotFinal with ⟨i, hi⟩
      exact ⟨0, by omega, i, hi⟩
  | succ n ih =>
      by_cases hxPrevious : x ∈ Set.range (H.block n).finalHole.vertex
      · have hxCurrentInitial :
            x ∈ Set.range (H.block (n + 1)).initialHole.vertex := by
          rw [← H.chain n]
          exact hxPrevious
        rcases (H.block (n + 1)).exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
            hxCurrentInitial hxNotFinal with ⟨i, hi⟩
        exact ⟨n + 1, by omega, i, hi⟩
      · rcases ih hxPrevious with ⟨r, hr, i, hi⟩
        exact ⟨r, by omega, i, hi⟩

end PathBlockHistory

namespace Lemma11AHistoryContext

variable {D : ConcretePathDeformation O Cprime}

/-- A represented concrete step removes `x`, either in the current block or in
one of the finite prior blocks. -/
def ContainsRemovedVertex
    (X : D.Lemma11AHistoryContext) (x : V) : Prop :=
  match X with
  | .first _ =>
      ∃ i : Fin D.deformation.stepCount,
        x = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex
  | .later H =>
      (∃ r : Nat, r < H.priorCount ∧
        ∃ i : Fin (H.history.block r).deformation.stepCount,
          x = ((H.history.block r).deformation.step i).before.vertex
            ((H.history.block r).deformation.step i).removedIndex) ∨
      ∃ i : Fin D.deformation.stepCount,
        x = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex

/-- A missing original-hole vertex is not merely on a represented path: it is
the removed vertex of a concrete represented step. -/
theorem containsRemovedVertex_of_mem_originalHole_of_not_mem_currentFinalHole
    (X : D.Lemma11AHistoryContext)
    {x : V}
    (hxOriginal : x ∈ Set.range X.originalHole.vertex)
    (hxNotFinal : x ∉ Set.range D.finalHole.vertex) :
    X.ContainsRemovedVertex x := by
  cases X with
  | first F =>
      change ∃ i : Fin D.deformation.stepCount,
        x = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex
      exact D.exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
        (by simpa [Lemma11AHistoryContext.originalHole] using hxOriginal)
        hxNotFinal
  | later H =>
      change
        (∃ r : Nat, r < H.priorCount ∧
          ∃ i : Fin (H.history.block r).deformation.stepCount,
            x = ((H.history.block r).deformation.step i).before.vertex
              ((H.history.block r).deformation.step i).removedIndex) ∨
        ∃ i : Fin D.deformation.stepCount,
          x = (D.deformation.step i).before.vertex
            (D.deformation.step i).removedIndex
      by_cases hxCurrentInitial : x ∈ Set.range D.initialHole.vertex
      · right
        exact D.exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
          hxCurrentInitial hxNotFinal
      · left
        let last : Nat := H.priorCount - 1
        have hlastLt : last < H.priorCount := by
          dsimp [last]
          have hpos := H.priorCount_pos
          omega
        have hxFirstInitial :
            x ∈ Set.range (H.history.block 0).initialHole.vertex := by
          simpa [Lemma11AHistoryContext.originalHole] using hxOriginal
        have hxNotLastFinal :
            x ∉ Set.range (H.history.block last).finalHole.vertex := by
          intro hxLast
          apply hxCurrentInitial
          rw [← H.final_before_current]
          simpa [last] using hxLast
        rcases H.history.exists_removedStep_through_of_mem_firstInitial_of_not_mem_finalHole
            last hxFirstInitial hxNotLastFinal with ⟨r, hr, i, hi⟩
        exact ⟨r, lt_of_le_of_lt hr hlastLt, i, hi⟩

end Lemma11AHistoryContext

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace OrderedOSExecution

/-- Positive-execution specialization on the exact manuscript terminal hole:
a missing initialized carrier vertex is removed by a concrete step represented
in the last block's finite history context. -/
theorem containsRemovedVertex_of_mem_originalHole_of_not_mem_manuscriptFinalHole
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount)
    {x : V}
    (hxOriginal : x ∈ Set.range originalHole.vertex)
    (hxNotFinal : x ∉ Set.range X.manuscriptFinalHole.vertex) :
    (X.blockContext (X.lastBlockIndex hpos)).ContainsRemovedVertex x := by
  have hxContext :
      x ∈ Set.range
        (X.blockContext (X.lastBlockIndex hpos)).originalHole.vertex := by
    rw [X.blockContext_originalHole (X.lastBlockIndex hpos)]
    exact hxOriginal
  have hxNotLastFinal :
      x ∉ Set.range
        (X.concreteBlock (X.lastBlockIndex hpos)).finalHole.vertex := by
    intro hxLast
    apply hxNotFinal
    rw [X.manuscriptFinalHole_eq_lastBlockFinalHole hpos]
    exact hxLast
  exact ConcretePathDeformation.Lemma11AHistoryContext.containsRemovedVertex_of_mem_originalHole_of_not_mem_currentFinalHole
    (X.blockContext (X.lastBlockIndex hpos)) hxContext hxNotLastFinal

end OrderedOSExecution

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
