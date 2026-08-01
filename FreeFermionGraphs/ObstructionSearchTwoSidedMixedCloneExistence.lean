import FreeFermionGraphs.ObstructionSearchTwoSidedMixedTypedClone

/-!
# Clone existence in mixed-side Lemma 11(a.ii)

The numerical part of Lemma 11(a.ii) has already been transported through a
literal mixed `ac`/`bd` history.  External degree three in the original hole
also supplies the underlying single-vertex-deformation clone independently of
its colour class.

This module proves that untyped clone existence uniformly for a first block or
a positive mixed-side history.  The remaining positive-history obligation is
to derive the clone pair's opposite fixed-pairing type from the mixed carrier
history.  No obstruction-search execution is constructed, and no conclusion
of Lemma 14 is assumed.
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

/-- Lemma 11(a.ii) up to the colour of the clone pair, uniformly for the first
path block and for a path preceded by a genuinely mixed-side history.

The forward implication derives the clone directly from degree three in the
manuscript's original hole.  The reverse implication only needs the numerical
degree equivalence, exactly as in the paper. -/
theorem lemma11aii_clone_exists
    (X : D.MixedSideLemma11AHistoryContext)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPrime : u ∈ Cprime)
    (hanti : D.path.AnticommutesWith u) :
    D.finalHole.externalDegree u = 4 ↔
      X.originalHole.externalDegree u = 3 ∧
        ∃ q : Fin X.originalHole.card,
          X.originalHole.SingleVertexDeformation u q := by
  have hdegree := X.lemma11aii_degree_iff hclaw hu huPrime hanti
  constructor
  · intro hfour
    have hthree : X.originalHole.externalDegree u = 3 :=
      hdegree.mp hfour
    have huOutside : u ∉ Set.range X.originalHole.vertex := by
      rintro ⟨q, rfl⟩
      have htwo := X.originalHole.externalDegree_vertex_eq_two q
      omega
    obtain ⟨q, hclone⟩ :=
      X.originalHole.exists_singleVertexDeformation_of_externalDegree_eq_three
        hclaw huOutside hthree
    exact ⟨hthree, q, hclone⟩
  · rintro ⟨hthree, _hclone⟩
    exact hdegree.mpr hthree

end MixedSideLemma11AHistoryContext

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
