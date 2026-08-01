import FreeFermionGraphs.ObstructionSearchFiniteMixedOrderedExecution
import FreeFermionGraphs.ObstructionSearchTwoSidedCanonicalEntry

/-!
# Canonical entries for finite mixed-side executions

The carrier of a Definition 19 path determines its first introduced endpoint:
the opposite endpoint is the final removed vertex and lies outside the fixed
prime carrier.  This module applies that local fact directly to the selected
side data stored by finite executions.

No cross-execution orientation certificate is assumed.  Equal path carriers
produce equal entries even when the two blocks use different `ac` or `bd`
presentations.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem reorient_firstIntroduced_eq
    {O : FixedPairingPathFamily G}
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide) :
    ((D.reorient side).deformation.step
        (D.reorient side).firstIndex).introduced =
      (D.deformation.step D.firstIndex).introduced := by
  cases side <;> rfl

/-- Equal path carriers have the same canonical first introduced endpoint,
using only the local data of each selected side. -/
theorem firstIntroduced_eq_of_reoriented_path_range_eq
    {O O' : FixedPairingPathFamily G}
    (D : ConcretePathDeformation O Cprime)
    (E : ConcretePathDeformation O' Cprime)
    (sideD sideE : DeformationSide)
    (F : (D.reorient sideD).FullDefinition19Lemma11AData)
    (H : (E.reorient sideE).FullDefinition19Lemma11AData)
    (hRange : Set.range D.path.vertex = Set.range E.path.vertex) :
    (D.deformation.step D.firstIndex).introduced =
      (E.deformation.step E.firstIndex).introduced := by
  let A : (D.reorient sideD).Lemma11AHistoryContext := .first F
  let B : (E.reorient sideE).Lemma11AHistoryContext := .first H
  have hOriented := A.firstIntroduced_eq_of_path_range_eq B (by
    simpa using hRange)
  rw [reorient_firstIntroduced_eq D sideD,
    reorient_firstIntroduced_eq E sideE] at hOriented
  exact hOriented

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace FiniteMixedSideOrderedOSExecution

/-- Equal path carriers in two finite ordered executions have equal canonical
entries, with no stored cross-trace premise. -/
theorem entry_eq_of_path_eq
    {source source' : I.Node}
    {originalHole : IndexedInducedHole G}
    (A : FiniteMixedSideOrderedOSExecution I source originalHole)
    (B : FiniteMixedSideOrderedOSExecution I source' originalHole)
    (i : Fin A.blockCount) (j : Fin B.blockCount)
    (hPath : A.path i = B.path j) :
    A.entry i = B.entry j := by
  unfold entry
  apply ConcretePathDeformation.firstIntroduced_eq_of_reoriented_path_range_eq
    (A.block i) (B.block j) (A.side i) (B.side j)
    (A.localData i) (B.localData j)
  simpa [path] using hPath

end FiniteMixedSideOrderedOSExecution

namespace InitializationFiniteMixedSideOSExecutionData

/-- Canonical entry equality for any common path in two initialized finite
executions.  Pairing equality is not needed for this local orientation fact. -/
theorem commonPath_entry_eq
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    {source source' : I.Node}
    (i : Fin (X.ordered source).blockCount)
    (j : Fin (X.ordered source').blockCount)
    (hPath : (X.ordered source).path i =
      (X.ordered source').path j) :
    (X.ordered source).entry i =
      (X.ordered source').entry j :=
  (X.ordered source).entry_eq_of_path_eq (X.ordered source') i j hPath

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
