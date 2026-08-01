import FreeFermionGraphs.ObstructionSearchTwoSidedMixedOriginalCarrier

/-!
# Exact mixed-side Lemma 11(a.ii) context

A Definition 19 path block is either the first block of the deformation or is
preceded by a positive mixed-side history.  The first-block typed-clone theorem
needs no additional global carrier datum.  In the positive case, Definition 19
must retain the fixed-original-hole label of every removed path vertex.

This module packages those two faithful cases in one indexed interface and
states the complete opposite-pairing conclusion of Lemma 11(a.ii).  It does not
construct the positive-history carrier invariant from the obstruction-search
loop and does not assume any conclusion of Lemma 14.
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

/-- The exact Definition 19 carrier datum needed by a uniform mixed-side
Lemma 11(a.ii) context.

For the first block there is no earlier carrier to recover.  For a later block,
the current removed vertices must retain their defining membership in the fixed
original hole. -/
inductive ExactDefinition19CarrierData :
    D.MixedSideLemma11AHistoryContext → Prop where
  | first
      (side : DeformationSide)
      (F : (D.reorient side).FullDefinition19Lemma11AData) :
      ExactDefinition19CarrierData (.first side F)
  | later
      (H : D.MixedSideFullDefinition19Lemma11AHistoryData)
      (hremoved : H.CurrentRemovedVerticesInOriginal) :
      ExactDefinition19CarrierData (.later H)

/-- Complete Lemma 11(a.ii), including the clone of pairing type opposite to
the fixed-pairing deformation, uniformly for a first block and a later block
with a genuine mixed-side Definition 19 history. -/
theorem lemma11aii_exact
    (X : D.MixedSideLemma11AHistoryContext)
    (hcarrier : ExactDefinition19CarrierData X)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      X.originalHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad X.originalHole u := by
  cases hcarrier with
  | first side F =>
      exact D.lemma11aii_of_firstBlock_mixedSide
        side F hclaw hu huPrime hanti
  | later H hremoved =>
      exact H.lemma11aii_exact_of_mixedSideHistory
        hremoved hclaw hu huPrime hanti

end MixedSideLemma11AHistoryContext

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
