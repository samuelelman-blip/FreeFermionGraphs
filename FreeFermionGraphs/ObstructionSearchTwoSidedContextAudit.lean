import FreeFermionGraphs.ObstructionSearchTwoSidedMechanicalReorientation

/-!
# Audit of the current two-sided Lemma 11 history context

A fixed-pairing deformation in Definition 19 may contain both `ac` and `bd`
path components.  The current `TwoSidedSearchPathHistoryWitness` records the
side of its current block, but its positive `Lemma11AHistoryContext` is still a
`PathBlockHistory` in one oriented family.  Consequently every prior block in
that context lies on the same selected component side as the current block.

This module makes that restriction explicit.  It is an audit theorem, not a
manuscript conclusion: the literal `OS` construction still needs a mixed-side
history interface before the current witness can serve as the final provenance
object for an arbitrary Definition 19 search trace.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace TwoSidedSearchPathHistoryWitness

/-- Membership in the `acPaths` family of the side-oriented presentation is
exactly membership in the component family selected by that side in the
original presentation.

This helper performs the side split before any dependent witness data is in
scope, avoiding dependent elimination on `A.side`. -/
private theorem mem_selectedSide_of_mem_oriented_ac
    (side : DeformationSide)
    {Q : Set V}
    (hQ : Q ∈ (side.family O).acPaths) :
    match side with
    | .ac => Q ∈ O.acPaths
    | .bd => Q ∈ O.bdPaths := by
  cases side with
  | ac =>
      simpa [DeformationSide.family] using hQ
  | bd =>
      simpa [DeformationSide.family, swapSides] using hQ

/-- Every prior block stored in the current positive history has the same
selected component side as the witness's current block.

This follows from the type of `FullDefinition19Lemma11AHistoryData`: all of its
blocks live in `A.side.family O`, and their local Definition 19 geometry presents
them as `ac` blocks in that oriented family. -/
theorem prior_path_mem_selectedSide
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    (H : A.block.FullDefinition19Lemma11AHistoryData)
    (r : Nat) :
    match A.side with
    | .ac => Set.range (H.history.block r).path.vertex ∈ O.acPaths
    | .bd => Set.range (H.history.block r).path.vertex ∈ O.bdPaths := by
  have hactive :
      Set.range (H.history.block r).path.vertex ∈
        (A.side.family O).acPaths := by
    rw [← (H.history.block r).activePath_eq
      (H.history.block r).firstIndex]
    exact
      ((H.prior r).neighborhood.mechanical.stepGeometry
        (H.history.block r).firstIndex).base.activePath_ac
  exact mem_selectedSide_of_mem_oriented_ac A.side hactive

/-- The execution-provenance field and the type-level history restriction
combine to show that every represented prior output path is on the witness's
selected side. -/
theorem prior_output_mem_selectedSide
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    (H : A.block.FullDefinition19Lemma11AHistoryData)
    (hcontext : A.context = .later H)
    {r : Nat} (hr : r < H.priorCount) :
    Set.range (H.history.block r).path.vertex ∈ S.paths ∧
      (match A.side with
      | .ac => Set.range (H.history.block r).path.vertex ∈ O.acPaths
      | .bd => Set.range (H.history.block r).path.vertex ∈ O.bdPaths) := by
  exact ⟨A.prior_output_mem H hcontext r hr,
    A.prior_path_mem_selectedSide H r⟩

end TwoSidedSearchPathHistoryWitness

end FixedPairingPathFamily

end SimpleGraph
