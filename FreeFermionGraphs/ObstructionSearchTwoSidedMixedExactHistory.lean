import FreeFermionGraphs.ObstructionSearchTwoSidedMixedLemma11AExact

/-!
# Exact mixed-side search histories

The paper's obstruction search must retain one carrier-level Definition 19
block for every appended path, together with the genuinely mixed earlier
history and the fixed-original-hole labels of the removed path vertices.

This module packages exactly that per-output-path provenance.  It upgrades the
older side-only history witness to an interface on which the complete statement
of Lemma 11(a.ii), including the opposite typed clone, is available directly.
It does not construct the interface from the current `OS` implementation and
does not assume any conclusion of Lemma 14.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

namespace MixedSideLemma11AHistoryContext

variable {D : ConcretePathDeformation O Cprime}

/-- Every earlier block represented by a later mixed context is an actual
output path of the same search.  There is no obligation for a first block. -/
def PriorPathsIn
    (X : D.MixedSideLemma11AHistoryContext)
    (S : SearchDeformation O Cprime) : Prop :=
  match X with
  | .first _ _ => True
  | .later H =>
      ∀ r : Nat, r < H.priorCount →
        Set.range (H.history.carrier.block r).path.vertex ∈ S.paths

end MixedSideLemma11AHistoryContext

/-- Paper-faithful provenance for one path output by the obstruction search.

Unlike `TwoSidedSearchPathHistoryWitness`, the concrete block remains in the
unswapped carrier family `O`.  Its current side is recorded by the mixed
context, so prior blocks may independently use either Definition 19 component
side.  `carrierData` retains the fixed-original-hole labels needed in the later
case of Lemma 11(a.ii). -/
structure ExactMixedSideSearchPathHistoryWitness
    (S : SearchDeformation O Cprime)
    (originalHole : IndexedInducedHole G)
    (P : Set V) where
  block : ConcretePathDeformation O Cprime
  context : block.MixedSideLemma11AHistoryContext
  carrierData : context.ExactDefinition19CarrierData
  path_eq : Set.range block.path.vertex = P
  output_mem : P ∈ S.paths
  prior_output_mem : context.PriorPathsIn S
  originalHole_eq : context.originalHole = originalHole

namespace ExactMixedSideSearchPathHistoryWitness

/-- The exact Lemma 11(a.ii) conclusion for a represented search-output path,
expressed using the fixed original hole of the search rather than the internal
context field. -/
theorem lemma11aii_exact
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : ExactMixedSideSearchPathHistoryWitness S originalHole P)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ A.block.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : A.block.path.AnticommutesWith u) :
    A.block.finalHole.externalDegree u = 4 ↔
      originalHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad originalHole u := by
  have h :=
    MixedSideLemma11AHistoryContext.lemma11aii_exact
      A.context A.carrierData hclaw hu huPrime hanti
  rw [A.originalHole_eq] at h
  exact h

end ExactMixedSideSearchPathHistoryWitness

/-- Exact mixed-side Definition 19 history data for every path output by one
search deformation. -/
structure ExactMixedSideSearchHistoryData
    (S : SearchDeformation O Cprime)
    (originalHole : IndexedInducedHole G) where
  witness : ∀ {P : Set V}, P ∈ S.paths →
    ExactMixedSideSearchPathHistoryWitness S originalHole P

namespace ExactMixedSideSearchHistoryData

/-- Every output path of an exact mixed-side history satisfies the complete
Lemma 11(a.ii) conclusion through its concrete carrier block. -/
theorem output_lemma11aii_exact
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    (H : ExactMixedSideSearchHistoryData S originalHole)
    {P : Set V} (hP : P ∈ S.paths)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ (H.witness hP).block.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : (H.witness hP).block.path.AnticommutesWith u) :
    (H.witness hP).block.finalHole.externalDegree u = 4 ↔
      originalHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad originalHole u :=
  (H.witness hP).lemma11aii_exact hclaw hu huPrime hanti

end ExactMixedSideSearchHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
