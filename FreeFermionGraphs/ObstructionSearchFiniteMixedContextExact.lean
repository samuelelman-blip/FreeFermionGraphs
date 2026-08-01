import FreeFermionGraphs.ObstructionSearchFiniteMixedSamePairing
import FreeFermionGraphs.ObstructionSearchFiniteMixedLemma11ATrace

/-!
# Exact Lemma 11(a.ii) from finite mixed-side contexts

The zero-or-positive finite context of a literal block contains exactly the
data needed for the opposite typed-clone conclusion of Lemma 11(a.ii).  The
first-block case uses the local mixed-side theorem and transports degree and
clone data across equality of the original-hole carrier.  The later case is
the existing bounded-prefix theorem.

This uniform theorem is exposed at initialized ordered indices for use by the
literal later-Definition-20 obstruction branch.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

namespace FiniteMixedSideLemma11AContext

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Exact Lemma 11(a.ii), including the opposite typed clone on the fixed
original hole, for a zero-or-positive finite mixed-side context. -/
theorem lemma11aii_exact
    (X : FiniteMixedSideLemma11AContext D originalHole)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      originalHole.externalDegree u = 3 ∧
        O.HasTypedClone .ad originalHole u := by
  cases X with
  | first side F hOriginal =>
      have hfirst :=
        D.lemma11aii_of_firstBlock_mixedSide
          side F hclaw hu huPrime hanti
      have hdegree :
          D.initialHole.externalDegree u =
            originalHole.externalDegree u :=
        D.initialHole.externalDegree_eq_of_range_eq
          originalHole hOriginal
      have htyped :
          O.HasTypedClone .ad D.initialHole u ↔
            O.HasTypedClone .ad originalHole u :=
        O.hasTypedClone_iff_of_range_eq .ad
          D.initialHole originalHole hOriginal u
      constructor
      · intro hfour
        obtain ⟨hthree, hclone⟩ := hfirst.mp hfour
        exact ⟨by
          rw [← hdegree]
          exact hthree, htyped.mp hclone⟩
      · rintro ⟨hthree, hclone⟩
        apply hfirst.mpr
        exact ⟨by
          rw [hdegree]
          exact hthree, htyped.mpr hclone⟩
  | later H =>
      exact H.lemma11aii_exact hclaw hu huPrime hanti

end FiniteMixedSideLemma11AContext

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace InitializationFiniteMixedSideOSExecutionData

/-- Exact Lemma 11(a.ii) for any actual block index of an initialized finite
execution. -/
theorem orderedBlock_lemma11aii_exact
    (X : I.InitializationFiniteMixedSideOSExecutionData)
    (source : I.Node)
    (i : Fin (X.ordered source).blockCount)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ ((X.ordered source).block i).dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : ((X.ordered source).block i).path.AnticommutesWith u) :
    ((X.ordered source).block i).finalHole.externalDegree u = 4 ↔
      X.originalHole.externalDegree u = 3 ∧
        (families (I.pairing source)).HasTypedClone
          .ad X.originalHole u :=
  (X.orderedContextAt source i).lemma11aii_exact
    hclaw hu huPrime hanti

end InitializationFiniteMixedSideOSExecutionData

end ObstructionSearchInitialization

end FixedPairingPathFamily

end SimpleGraph
