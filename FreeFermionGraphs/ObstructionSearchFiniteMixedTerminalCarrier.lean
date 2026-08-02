import FreeFermionGraphs.ObstructionSearchFiniteMixedTerminalFinalClones
import FreeFermionGraphs.ObstructionSearchFiniteMixedPersistence
import FreeFermionGraphs.ObstructionSearchTerminalRemovedOccurrence

/-!
# Carrier persistence and concrete removal on finite mixed-side histories

The terminal tether argument uses two complementary facts.  A vertex on the
initialized original hole which avoids every represented path persists to the
last block's final hole.  Conversely, if such a vertex is absent from that
final hole, some concrete represented deformation step removes it.

Both statements are proved directly on the bounded `Fin priorCount` history.
No total `Nat`-indexed tail or terminal conclusion is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

namespace FiniteMixedSideLemma11AContext

/-- A vertex avoids the current path and every actual prior path represented by
the bounded finite context. -/
def AvoidsAllPaths
    (X : FiniteMixedSideLemma11AContext D originalHole) (x : V) : Prop :=
  match X with
  | .first _ _ _ => x ∉ Set.range D.path.vertex
  | .later H =>
      (∀ r : Fin H.priorCount,
        x ∉ Set.range (H.priorBlock r).path.vertex) ∧
      x ∉ Set.range D.path.vertex

/-- An initialized carrier vertex which avoids every represented finite path
remains on the current block's final hole. -/
theorem mem_currentFinalHole_of_mem_originalHole_of_avoids
    (X : FiniteMixedSideLemma11AContext D originalHole)
    {x : V}
    (hx : x ∈ Set.range originalHole.vertex)
    (havoid : X.AvoidsAllPaths x) :
    x ∈ Set.range D.finalHole.vertex := by
  cases X with
  | first side current hinitial =>
      apply D.mem_finalHole_of_mem_initialHole_of_not_mem_path
      · rw [hinitial]
        exact hx
      · simpa [AvoidsAllPaths] using havoid
  | later H =>
      rcases havoid with ⟨hprior, hcurrent⟩
      have hxFirstInitial :
          x ∈ Set.range
            (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.vertex := by
        rw [H.firstInitial_eq_original]
        exact hx
      have hxFirstFinal :
          x ∈ Set.range
            (H.priorBlock ⟨0, H.priorCount_pos⟩).finalHole.vertex :=
        (H.priorBlock ⟨0, H.priorCount_pos⟩).mem_finalHole_of_mem_initialHole_of_not_mem_path
          hxFirstInitial (hprior ⟨0, H.priorCount_pos⟩)
      have hxLastFinal :
          x ∈ Set.range (H.priorBlock H.lastIndex).finalHole.vertex := by
        apply H.mem_finalHole_of_mem_finalHole_through
          (r := 0) (n := H.lastIndex.val)
          H.priorCount_pos H.lastIndex.isLt (by omega) hxFirstFinal
        intro q hq hqpos hqle
        exact hprior ⟨q, hq⟩
      have hxCurrentInitial : x ∈ Set.range D.initialHole.vertex := by
        rw [← H.lastFinal_eq_current']
        exact hxLastFinal
      exact D.mem_finalHole_of_mem_initialHole_of_not_mem_path
        hxCurrentInitial hcurrent

/-- A represented concrete step removes `x`, either in an actual prior block or
in the current block. -/
def ContainsRemovedVertex
    (X : FiniteMixedSideLemma11AContext D originalHole) (x : V) : Prop :=
  match X with
  | .first _ _ _ =>
      ∃ i : Fin D.deformation.stepCount,
        x = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex
  | .later H =>
      (∃ r : Fin H.priorCount,
        ∃ i : Fin (H.priorBlock r).deformation.stepCount,
          x = ((H.priorBlock r).deformation.step i).before.vertex
            ((H.priorBlock r).deformation.step i).removedIndex) ∨
      ∃ i : Fin D.deformation.stepCount,
        x = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex

end FiniteMixedSideLemma11AContext

namespace FiniteMixedSideLemma11AHistoryData

/-- If a vertex starts on the first prior carrier and is absent from the final
hole of prior block `n`, then one of the first `n+1` actual finite blocks
removes it at a concrete step. -/
theorem exists_removedStep_through_of_mem_firstInitial_of_not_mem_finalHole
    (H : FiniteMixedSideLemma11AHistoryData D originalHole)
    {x : V} (n : Nat) (hn : n < H.priorCount)
    (hxInitial :
      x ∈ Set.range
        (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.vertex)
    (hxNotFinal :
      x ∉ Set.range (H.priorBlock ⟨n, hn⟩).finalHole.vertex) :
    ∃ r : Nat, ∃ hr : r < H.priorCount,
      r ≤ n ∧
        ∃ i : Fin (H.priorBlock ⟨r, hr⟩).deformation.stepCount,
          x = ((H.priorBlock ⟨r, hr⟩).deformation.step i).before.vertex
            ((H.priorBlock ⟨r, hr⟩).deformation.step i).removedIndex := by
  induction n generalizing hn with
  | zero =>
      rcases (H.priorBlock ⟨0, H.priorCount_pos⟩).exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
          hxInitial (by simpa using hxNotFinal) with ⟨i, hi⟩
      exact ⟨0, H.priorCount_pos, by omega, i, hi⟩
  | succ n ih =>
      have hnPrev : n < H.priorCount := by omega
      let previous : Fin H.priorCount := ⟨n, hnPrev⟩
      let current : Fin H.priorCount := ⟨n + 1, hn⟩
      by_cases hxPrevious :
          x ∈ Set.range (H.priorBlock previous).finalHole.vertex
      · have hxCurrentInitial :
            x ∈ Set.range (H.priorBlock current).initialHole.vertex := by
          have hchain := H.priorChain
            (r := previous) (q := current) (by
              simp [previous, current])
          rw [← hchain]
          exact hxPrevious
        rcases (H.priorBlock current).exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
            hxCurrentInitial (by simpa [current] using hxNotFinal) with
          ⟨i, hi⟩
        exact ⟨n + 1, hn, by omega, i, by simpa [current] using hi⟩
      · rcases ih hnPrev (by simpa [previous] using hxPrevious) with
          ⟨r, hr, hrle, i, hi⟩
        exact ⟨r, hr, by omega, i, hi⟩

end FiniteMixedSideLemma11AHistoryData

namespace FiniteMixedSideLemma11AContext

/-- A missing initialized carrier vertex is removed by a concrete step in the
bounded finite context. -/
theorem containsRemovedVertex_of_mem_originalHole_of_not_mem_currentFinalHole
    (X : FiniteMixedSideLemma11AContext D originalHole)
    {x : V}
    (hxOriginal : x ∈ Set.range originalHole.vertex)
    (hxNotFinal : x ∉ Set.range D.finalHole.vertex) :
    X.ContainsRemovedVertex x := by
  cases X with
  | first side current hinitial =>
      change ∃ i : Fin D.deformation.stepCount,
        x = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex
      exact D.exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
        (by rw [hinitial]; exact hxOriginal) hxNotFinal
  | later H =>
      change
        (∃ r : Fin H.priorCount,
          ∃ i : Fin (H.priorBlock r).deformation.stepCount,
            x = ((H.priorBlock r).deformation.step i).before.vertex
              ((H.priorBlock r).deformation.step i).removedIndex) ∨
        ∃ i : Fin D.deformation.stepCount,
          x = (D.deformation.step i).before.vertex
            (D.deformation.step i).removedIndex
      by_cases hxCurrentInitial : x ∈ Set.range D.initialHole.vertex
      · exact Or.inr
          (D.exists_removedStep_of_mem_initialHole_of_not_mem_finalHole
            hxCurrentInitial hxNotFinal)
      · have hxFirstInitial :
            x ∈ Set.range
              (H.priorBlock ⟨0, H.priorCount_pos⟩).initialHole.vertex := by
          rw [H.firstInitial_eq_original]
          exact hxOriginal
        have hxNotLastFinal :
            x ∉ Set.range (H.priorBlock H.lastIndex).finalHole.vertex := by
          intro hxLast
          apply hxCurrentInitial
          rw [← H.lastFinal_eq_current']
          exact hxLast
        rcases H.exists_removedStep_through_of_mem_firstInitial_of_not_mem_finalHole
            H.lastIndex.val H.lastIndex.isLt hxFirstInitial hxNotLastFinal with
          ⟨r, hr, _hrle, i, hi⟩
        exact Or.inl ⟨⟨r, hr⟩, i, hi⟩

end FiniteMixedSideLemma11AContext

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace InitializationFiniteMixedSideOSExecutionData

/-- Carrier persistence specialized to the last actual block of a positive
finite initialized execution. -/
theorem mem_lastBlockFinalHole_of_mem_originalHole_of_avoidsContext
    (Y : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (hpos : 0 < (Y.ordered source).blockCount)
    {x : V}
    (hx : x ∈ Set.range Y.originalHole.vertex)
    (havoid :
      (Y.orderedContextAt source
        ((Y.ordered source).lastBlockIndex hpos)).AvoidsAllPaths x) :
    x ∈ Set.range
      ((Y.ordered source).block
        ((Y.ordered source).lastBlockIndex hpos)).finalHole.vertex :=
  ConcretePathDeformation.FiniteMixedSideLemma11AContext.mem_currentFinalHole_of_mem_originalHole_of_avoids
    (Y.orderedContextAt source
      ((Y.ordered source).lastBlockIndex hpos)) hx havoid

/-- The same persistence conclusion on the exact finite manuscript terminal
hole. -/
theorem mem_manuscriptFinalHole_of_mem_originalHole_of_avoidsContext
    (Y : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (hpos : 0 < (Y.ordered source).blockCount)
    {x : V}
    (hx : x ∈ Set.range Y.originalHole.vertex)
    (havoid :
      (Y.orderedContextAt source
        ((Y.ordered source).lastBlockIndex hpos)).AvoidsAllPaths x) :
    x ∈ Set.range (Y.ordered source).manuscriptFinalHole.vertex := by
  rw [(Y.ordered source).manuscriptFinalHole_eq_lastBlockFinalHole hpos]
  exact Y.mem_lastBlockFinalHole_of_mem_originalHole_of_avoidsContext
    source hpos hx havoid

/-- If an initialized original-hole vertex is missing from the exact positive
terminal hole, a concrete step represented by the last finite context removes
it. -/
theorem containsRemovedVertex_of_mem_originalHole_of_not_mem_manuscriptFinalHole
    (Y : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (hpos : 0 < (Y.ordered source).blockCount)
    {x : V}
    (hxOriginal : x ∈ Set.range Y.originalHole.vertex)
    (hxNotFinal : x ∉ Set.range (Y.ordered source).manuscriptFinalHole.vertex) :
    (Y.orderedContextAt source
      ((Y.ordered source).lastBlockIndex hpos)).ContainsRemovedVertex x := by
  have hxNotLast :
      x ∉ Set.range
        ((Y.ordered source).block
          ((Y.ordered source).lastBlockIndex hpos)).finalHole.vertex := by
    intro hx
    apply hxNotFinal
    rw [(Y.ordered source).manuscriptFinalHole_eq_lastBlockFinalHole hpos]
    exact hx
  exact ConcretePathDeformation.FiniteMixedSideLemma11AContext.containsRemovedVertex_of_mem_originalHole_of_not_mem_currentFinalHole
    (Y.orderedContextAt source
      ((Y.ordered source).lastBlockIndex hpos)) hxOriginal hxNotLast

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
