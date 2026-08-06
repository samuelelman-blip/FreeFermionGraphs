import FreeFermionGraphs.Lemma16OccurrenceTransport

/-!
# Manuscript Lemma 16 from a completed finite Definition 19 trace

A completed literal trace retains the fixed indexed prime hole, the exact
successor relation between consecutive steps of each path block, and the
component-maximal endpoint clause at the last step of each block.  These are
Definition 19 execution data, not a reverse deformation or the Lemma 12
criterion.

From them this module constructs `Lemma12Definition19Data`, derives the
Corollaries 9--10 occurrence transport from the underlying finite trace, and
exports the unqualified manuscript theorem `paperLemma16`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem reorient_step_removedVertex_eq
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (i : Fin D.deformation.stepCount) :
    ((D.reorient side).deformation.step i).before.vertex
        ((D.reorient side).deformation.step i).removedIndex =
      (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex := by
  cases side <;> rfl

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Literal Definition 19 data needed after the finite trace has terminated.

The prime hole is stored as an indexed induced hole because the set-valued
parameter `Cprime` forgets its cyclic order.  `stepIndex_consecutive` states
that consecutive local replacements remain consecutive in the flattened run.
`terminalEndpointMaximal` is the component-maximality clause for the terminal
removed vertex of every path block. -/
structure PaperLemma16Trace
    (X : FiniteMixedSideSearchTrace S originalHole) where
  primeHole : IndexedInducedHole G
  primeHole_carrier : Set.range primeHole.vertex = Cprime
  primeHole_even : Even primeHole.card
  stepIndex_consecutive :
    ∀ (i : Fin X.blockCount)
      (s t : Fin (X.block i).deformation.stepCount),
      s.val + 1 = t.val →
        (X.stepIndex i s).val + 1 = (X.stepIndex i t).val
  terminalEndpointMaximal :
    ∀ (i : Fin X.blockCount) {v : V},
      v ∈ Cprime →
      G.Adj
        ((X.block i).deformation.step (X.block i).lastIndex).before.vertex
          ((X.block i).deformation.step
            (X.block i).lastIndex).removedIndex
        v →
      v ∈ Set.range (X.block i).path.vertex

namespace PaperLemma16Trace

variable {X : FiniteMixedSideSearchTrace S originalHole}

/-- Every vertex of a trace path is one of the introduced or removed
coordinates of that same block. -/
theorem pathVertex_eq_introduced_or_removed
    (Y : X.PaperLemma16Trace)
    (i : Fin X.blockCount)
    (q : Fin (X.block i).path.card) :
    (∃ s : Fin (X.block i).deformation.stepCount,
      (X.block i).path.vertex q =
        ((X.block i).deformation.step s).introduced) ∨
    (∃ s : Fin (X.block i).deformation.stepCount,
      (X.block i).path.vertex q =
        ((X.block i).deformation.step s).before.vertex
          ((X.block i).deformation.step s).removedIndex) := by
  let D := X.orientedBlock i
  let qD : Fin D.path.card :=
    ⟨q.val, by
      simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using q.isLt⟩
  rcases D.pathIndex_introduced_or_removed
      (X.localData i).neighborhood.pathOrder
      (X.localData i).path_card_eq qD with hintroduced | hremoved
  · obtain ⟨sD, hq⟩ := hintroduced
    let s : Fin (X.block i).deformation.stepCount :=
      ⟨sD.val, by
        simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using sD.isLt⟩
    left
    refine ⟨s, ?_⟩
    have hD :
        D.path.vertex qD = (D.deformation.step sD).introduced := by
      rw [hq]
      exact (X.localData i).neighborhood.pathOrder.introduced_eq sD
    cases hside : X.side i <;>
      simpa [D, qD, s, hside,
        FiniteMixedSideSearchTrace.orientedBlock,
        ConcretePathDeformation.reorient,
        ConcreteDeformation.reorient,
        ConcreteDeformationStep.reorient] using hD
  · obtain ⟨sD, hq⟩ := hremoved
    let s : Fin (X.block i).deformation.stepCount :=
      ⟨sD.val, by
        simpa [D, FiniteMixedSideSearchTrace.orientedBlock] using sD.isLt⟩
    right
    refine ⟨s, ?_⟩
    have hD :
        D.path.vertex qD =
          (D.deformation.step sD).before.vertex
            (D.deformation.step sD).removedIndex := by
      rw [hq]
      exact (X.localData i).neighborhood.pathOrder.removed_eq sD
    cases hside : X.side i <;>
      simpa [D, qD, s, hside,
        FiniteMixedSideSearchTrace.orientedBlock,
        ConcretePathDeformation.reorient,
        ConcreteDeformation.reorient,
        ConcreteDeformationStep.reorient] using hD

/-- Every flattened active path is contained in the actual deformation
boundary. -/
theorem activePath_subset_boundary
    (Y : X.PaperLemma16Trace) :
    ∀ k : Fin X.flattened.deformation.stepCount,
      Set.range (X.flattened.deformation.step k).activePath.vertex ⊆
        X.flattened.boundary := by
  intro k x hx
  obtain ⟨i, s, his⟩ := X.stepIndex_surjective k
  subst k
  have hxPath : x ∈ Set.range (X.block i).path.vertex := by
    rw [X.step_eq i s, X.block i |>.activePath_eq s] at hx
    exact hx
  obtain ⟨q, hqx⟩ := hxPath
  rcases Y.pathVertex_eq_introduced_or_removed i q with
      ⟨t, ht⟩ | ⟨t, ht⟩
  · apply X.flattened.mem_boundary_iff.mpr
    refine ⟨X.stepIndex i t, Or.inl ?_⟩
    calc
      x = (X.block i).path.vertex q := hqx.symm
      _ = ((X.block i).deformation.step t).introduced := ht
      _ = (X.flattened.deformation.step (X.stepIndex i t)).introduced :=
        (congrArg ConcreteDeformationStep.introduced
          (X.step_eq i t)).symm
  · apply X.flattened.mem_boundary_iff.mpr
    refine ⟨X.stepIndex i t, Or.inr ?_⟩
    calc
      x = (X.block i).path.vertex q := hqx.symm
      _ = ((X.block i).deformation.step t).before.vertex
          ((X.block i).deformation.step t).removedIndex := ht
      _ = (X.flattened.deformation.step (X.stepIndex i t)).before.vertex
          (X.flattened.deformation.step
            (X.stepIndex i t)).removedIndex := by
        have hstep := X.step_eq i t
        exact (congrArg
          (fun z : ConcreteDeformationStep O Cprime =>
            z.before.vertex z.removedIndex) hstep).symm

/-- Every flattened removed vertex belongs to the fixed original hole. -/
theorem removed_mem_original
    (Y : X.PaperLemma16Trace) :
    ∀ k : Fin X.flattened.deformation.stepCount,
      (X.flattened.deformation.step k).before.vertex
          (X.flattened.deformation.step k).removedIndex ∈
        Set.range X.flattened.initialHole.vertex := by
  intro k
  obtain ⟨i, s, his⟩ := X.stepIndex_surjective k
  subst k
  have hraw := X.removed_mem_original i s
  have hinitial :
      Set.range X.flattened.initialHole.vertex =
        Set.range originalHole.vertex := by
    calc
      Set.range X.flattened.initialHole.vertex =
          Set.range (X.block X.firstIndex).initialHole.vertex := by
        rw [FullDefinition19Deformation.initialHole]
        have hfirst := X.stepIndex_surjective
          (⟨0, X.flattened.nonempty⟩ :
            Fin X.flattened.deformation.stepCount)
        obtain ⟨j, t, hjt⟩ := hfirst
        have hzero : (X.stepIndex j t).val = 0 := by simpa [hjt]
        have hj : j = X.firstIndex := by
          apply Fin.ext
          by_contra hne
          have hpos : 0 < j.val := by omega
          have horder := X.stepIndex_order X.firstIndex j
            (X.block X.firstIndex).firstIndex t (Or.inl hpos)
          have hfirstNonneg :=
            (X.stepIndex X.firstIndex
              (X.block X.firstIndex).firstIndex).isLt
          omega
        subst j
        have ht : t = (X.block X.firstIndex).firstIndex := by
          apply Fin.ext
          by_contra hne
          have htpos : 0 < t.val := by
            have htLt := t.isLt
            dsimp [ConcretePathDeformation.firstIndex]
            omega
          have horder := X.stepIndex_order X.firstIndex X.firstIndex
            (X.block X.firstIndex).firstIndex t
            (Or.inr ⟨rfl, htpos⟩)
          omega
        subst t
        rw [X.step_eq]
        rfl
      _ = Set.range originalHole.vertex := X.originalHole_eq
  rw [hinitial]
  have hstep := X.step_eq i s
  simpa only [hstep] using hraw

/-- Consecutive local steps of one block give the exact continuation data
used in the interior branch of Lemma 12. -/
def continuation
    (Y : X.PaperLemma16Trace)
    (i : Fin X.blockCount)
    (s t : Fin (X.block i).deformation.stepCount)
    (hst : s.val + 1 = t.val) :
    FullDefinition19Deformation.Lemma12Continuation
      X.flattened (X.stepIndex i s) where
  next := X.stepIndex i t
  consecutive := Y.stepIndex_consecutive i s t hst
  samePath := by
    rw [X.step_eq i t, X.step_eq i s,
      (X.block i).activePath_eq t,
      (X.block i).activePath_eq s]
  removed_adj_nextIntroduced := by
    let A := (X.block i).reorient (X.side i)
    let L := (X.localData i).neighborhood.pathOrder
    have hpath :
        G.Adj
          (A.path.vertex (L.removedPathIndex s))
          (A.path.vertex (L.introducedPathIndex t)) := by
      apply (A.path.adj_iff _ _).2
      left
      rw [L.removed_index_val, L.introduced_index_val]
      omega
    rw [L.removed_eq s, L.introduced_eq t] at hpath
    rw [reorient_step_removedVertex_eq,
      (X.block i).reorient_step_introduced] at hpath
    simpa only [X.step_eq i s, X.step_eq i t] using hpath
  introduced_ne_nextIntroduced := by
    intro heq
    let A := (X.block i).reorient (X.side i)
    let L := (X.localData i).neighborhood.pathOrder
    have hpathEq :
        A.path.vertex (L.introducedPathIndex s) =
          A.path.vertex (L.introducedPathIndex t) := by
      rw [L.introduced_eq s, L.introduced_eq t,
        (X.block i).reorient_step_introduced,
        (X.block i).reorient_step_introduced]
      simpa only [X.step_eq i s, X.step_eq i t] using heq
    have hindex := A.path.injective hpathEq
    have hval := congrArg Fin.val hindex
    rw [L.introduced_index_val, L.introduced_index_val] at hval
    omega
  introduced_ne_nextRemoved := by
    intro heq
    let A := (X.block i).reorient (X.side i)
    let L := (X.localData i).neighborhood.pathOrder
    have hpathEq :
        A.path.vertex (L.introducedPathIndex s) =
          A.path.vertex (L.removedPathIndex t) := by
      rw [L.introduced_eq s, L.removed_eq t,
        (X.block i).reorient_step_introduced,
        reorient_step_removedVertex_eq]
      simpa only [X.step_eq i s, X.step_eq i t] using heq
    have hindex := A.path.injective hpathEq
    have hval := congrArg Fin.val hindex
    rw [L.introduced_index_val, L.removed_index_val] at hval
    omega
  introduced_not_adj_nextIntroduced := by
    intro hadj
    let A := (X.block i).reorient (X.side i)
    let L := (X.localData i).neighborhood.pathOrder
    have hpathAdj :
        G.Adj
          (A.path.vertex (L.introducedPathIndex s))
          (A.path.vertex (L.introducedPathIndex t)) := by
      rw [L.introduced_eq s, L.introduced_eq t,
        (X.block i).reorient_step_introduced,
        (X.block i).reorient_step_introduced]
      simpa only [X.step_eq i s, X.step_eq i t] using hadj
    have hindices := (A.path.adj_iff _ _).1 hpathAdj
    rw [L.introduced_index_val, L.introduced_index_val] at hindices
    omega
  introduced_not_adj_nextRemoved := by
    intro hadj
    let A := (X.block i).reorient (X.side i)
    let L := (X.localData i).neighborhood.pathOrder
    have hpathAdj :
        G.Adj
          (A.path.vertex (L.introducedPathIndex s))
          (A.path.vertex (L.removedPathIndex t)) := by
      rw [L.introduced_eq s, L.removed_eq t,
        (X.block i).reorient_step_introduced,
        reorient_step_removedVertex_eq]
      simpa only [X.step_eq i s, X.step_eq i t] using hadj
    have hindices := (A.path.adj_iff _ _).1 hpathAdj
    rw [L.introduced_index_val, L.removed_index_val] at hindices
    omega

/-- The endpoint/continuation alternative for every flattened step is derived
from its literal block occurrence. -/
theorem endpoint_or_continuation
    (Y : X.PaperLemma16Trace) :
    ∀ k : Fin X.flattened.deformation.stepCount,
      (∀ {v : V}, v ∈ Cprime →
        G.Adj
          ((X.flattened.deformation.step k).before.vertex
            (X.flattened.deformation.step k).removedIndex) v →
        v ∈ Set.range
          (X.flattened.deformation.step k).activePath.vertex) ∨
      Nonempty
        (FullDefinition19Deformation.Lemma12Continuation X.flattened k) := by
  intro k
  obtain ⟨i, s, his⟩ := X.stepIndex_surjective k
  subst k
  by_cases hlast : s.val + 1 = (X.block i).deformation.stepCount
  · left
    intro v hv hadj
    have hsLast : s = (X.block i).lastIndex := by
      apply Fin.ext
      dsimp [ConcretePathDeformation.lastIndex]
      omega
    have hrawAdj :
        G.Adj
          ((X.block i).deformation.step (X.block i).lastIndex).before.vertex
            ((X.block i).deformation.step
              (X.block i).lastIndex).removedIndex v := by
      rw [← hsLast]
      simpa only [X.step_eq i s] using hadj
    have hvPath := Y.terminalEndpointMaximal i hv hrawAdj
    rw [X.step_eq i s, (X.block i).activePath_eq s]
    exact hvPath
  · right
    have htLt : s.val + 1 < (X.block i).deformation.stepCount := by
      have hsLt := s.isLt
      omega
    let t : Fin (X.block i).deformation.stepCount :=
      ⟨s.val + 1, htLt⟩
    exact ⟨Y.continuation i s t rfl⟩

/-- The literal completed trace constructs the exact data consumed by Lemma
12.  No criterion or reverse run is stored in the trace. -/
def toLemma12Definition19Data
    (Y : X.PaperLemma16Trace) :
    X.flattened.Lemma12Definition19Data where
  primeHole := Y.primeHole
  primeHole_carrier := Y.primeHole_carrier
  primeHole_even := Y.primeHole_even
  removed_mem_original := Y.removed_mem_original
  activePath_subset_boundary := Y.activePath_subset_boundary
  endpoint_or_continuation := Y.endpoint_or_continuation

/-- Exact paper-facing conclusion, now independent of an externally supplied
Lemma 12 certificate. -/
def PaperLemma16Conclusion
    (Y : X.PaperLemma16Trace) : Prop :=
  X.flattened.dependentUnion ⊆
      Set.range X.flattened.terminalHole.vertex ∧
    ∃ finalHole : IndexedInducedHole G,
      FullDefinition19Deformation.ReverseRun
        X.flattened Y.primeHole 0 finalHole

/-- Manuscript Lemma 16.  Unobstructedness excludes every terminal-external
dependent vertex; the occurrence-indexed Corollaries 9--10 argument transports
Lemma 11(b)'s earlier witness; and the completed literal trace constructs the
palindromic reverse run through Lemma 12. -/
theorem paperLemma16
    (Y : X.PaperLemma16Trace)
    (hclaw : G.IsClawFree)
    (hunobstructed : X.IsUnobstructed) :
    Y.PaperLemma16Conclusion := by
  let L : X.flattened.Lemma12Definition19Data :=
    Y.toLemma12Definition19Data
  let T : X.Lemma16TerminalPathTransportData :=
    X.terminalPathTransportData hclaw
  have hcriterion :=
    X.dependentUnion_subset_terminal_of_unobstructed
      T hclaw hunobstructed
  refine ⟨hcriterion, ?_⟩
  simpa [L] using X.flattened.lemma12 L hclaw hcriterion

end PaperLemma16Trace
end FiniteMixedSideSearchTrace
end ConcretePathDeformation
end FixedPairingPathFamily
end SimpleGraph
