import FreeFermionGraphs.ObstructionSearchTerminalLastBlockGeometry

/-!
# Lemma 14(iv): persistence through the terminal execution history

The proof that the stopping path's `C_b` vertices lie in the terminal hole uses
only carrier persistence: such a vertex starts on the initialized original hole
and is removed by none of the path blocks preceding termination.

This module proves that transport for the finite Definition 19 history already
stored in `Lemma11AHistoryContext`.  It adds no terminal-path or tether
certificate.  The remaining search-specific task is to show that the relevant
vertices start on the original hole and avoid every recorded path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}
  {D : ConcretePathDeformation O Cprime}

namespace Lemma11AHistoryContext

/-- A vertex avoids the current path and, in the positive-history case, every
prior path block represented by the context. -/
def AvoidsAllPaths
    (X : D.Lemma11AHistoryContext) (x : V) : Prop :=
  match X with
  | .first _ => x ∉ Set.range D.path.vertex
  | .later H =>
      (∀ r : Nat, r < H.priorCount →
        x ∉ Set.range (H.history.block r).path.vertex) ∧
      x ∉ Set.range D.path.vertex

/-- A vertex on the original hole which avoids every path represented by a
finite Definition 19 history remains on the current block's final hole. -/
theorem mem_currentFinalHole_of_mem_originalHole_of_avoids
    (X : D.Lemma11AHistoryContext) {x : V}
    (hx : x ∈ Set.range X.originalHole.vertex)
    (havoid : X.AvoidsAllPaths x) :
    x ∈ Set.range D.finalHole.vertex := by
  cases X with
  | first F =>
      apply D.mem_finalHole_of_mem_initialHole_of_not_mem_path
      · simpa [Lemma11AHistoryContext.originalHole] using hx
      · simpa [AvoidsAllPaths] using havoid
  | later H =>
      have hxOriginal :
          x ∈ Set.range (H.history.block 0).initialHole.vertex := by
        simpa [Lemma11AHistoryContext.originalHole] using hx
      have hparts :
          (∀ r : Nat, r < H.priorCount →
            x ∉ Set.range (H.history.block r).path.vertex) ∧
          x ∉ Set.range D.path.vertex := by
        simpa [AvoidsAllPaths] using havoid
      rcases hparts with ⟨hprior, hcurrent⟩
      let last : Nat := H.priorCount - 1
      have hlastLt : last < H.priorCount := by
        dsimp [last]
        have hpos := H.priorCount_pos
        omega
      have hxFirstFinal :
          x ∈ Set.range (H.history.block 0).finalHole.vertex :=
        (H.history.block 0).mem_finalHole_of_mem_initialHole_of_not_mem_path
          hxOriginal (hprior 0 H.priorCount_pos)
      have hxLastFinal :
          x ∈ Set.range (H.history.block last).finalHole.vertex := by
        apply H.history.mem_finalHole_of_mem_finalHole_through
          (r := 0) (n := last) (Nat.zero_le last) hxFirstFinal
        intro q hqPos hqLast
        exact hprior q (by omega)
      have hxCurrentInitial : x ∈ Set.range D.initialHole.vertex := by
        rw [← H.final_before_current]
        exact hxLastFinal
      exact D.mem_finalHole_of_mem_initialHole_of_not_mem_path
        hxCurrentInitial hcurrent

end Lemma11AHistoryContext

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace OrderedOSExecution

/-- Carrier persistence specialized to the last concrete block of a positive
initialized execution. -/
theorem mem_lastBlockFinalHole_of_mem_originalHole_of_avoidsContext
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount) {x : V}
    (hx : x ∈ Set.range originalHole.vertex)
    (havoid :
      (X.blockContext (X.lastBlockIndex hpos)).AvoidsAllPaths x) :
    x ∈ Set.range
      (X.concreteBlock (X.lastBlockIndex hpos)).finalHole.vertex := by
  have hxContext :
      x ∈ Set.range
        (X.blockContext (X.lastBlockIndex hpos)).originalHole.vertex := by
    rw [X.blockContext_originalHole (X.lastBlockIndex hpos)]
    exact hx
  exact
    ConcretePathDeformation.Lemma11AHistoryContext.mem_currentFinalHole_of_mem_originalHole_of_avoids
      (X.blockContext (X.lastBlockIndex hpos)) hxContext havoid

/-- The same persistence conclusion stated on the exact manuscript terminal
hole `C_j^(m)`. -/
theorem mem_manuscriptFinalHole_of_mem_originalHole_of_avoidsContext
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : OrderedOSExecution I source originalHole)
    (hpos : 0 < X.blockCount) {x : V}
    (hx : x ∈ Set.range originalHole.vertex)
    (havoid :
      (X.blockContext (X.lastBlockIndex hpos)).AvoidsAllPaths x) :
    x ∈ Set.range X.manuscriptFinalHole.vertex := by
  rw [X.manuscriptFinalHole_eq_lastBlockFinalHole hpos]
  exact X.mem_lastBlockFinalHole_of_mem_originalHole_of_avoidsContext
    hpos hx havoid

end OrderedOSExecution

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
