import FreeFermionGraphs.Corollary11

/-!
# Corollary 11: component comparison

Two fixed-pairing deformations of the same type draw their paths from the
connected components of the same two induced bipartite graphs.  Consequently,
a component from one deformation and a component on the same side from the
other are either equal or disjoint.

The current `FixedPairingPathFamily` structure records component
disjointness inside one deformation.  `SameComponentGeometry` records the
corresponding cross-deformation fact needed by Corollary 11.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- Two deformation families use the same coloring data and their path sets
are drawn from the same connected-component partitions.

The overlap fields are the extensional property of connected components:
two components of the same induced graph that share a vertex are equal. -/
structure SameComponentGeometry
    (O O' : FixedPairingPathFamily G) : Prop where
  sameType : O.SameFixedPairingType O'
  ac_eq_of_overlap :
    ∀ ⦃P Q : Set V⦄,
      P ∈ O.acPaths →
      Q ∈ O'.acPaths →
      (∃ v, v ∈ P ∧ v ∈ Q) →
      P = Q
  bd_eq_of_overlap :
    ∀ ⦃P Q : Set V⦄,
      P ∈ O.bdPaths →
      Q ∈ O'.bdPaths →
      (∃ v, v ∈ P ∧ v ∈ Q) →
      P = Q

/-- Cross-deformation component geometry is symmetric. -/
theorem SameComponentGeometry.symm
    {O O' : FixedPairingPathFamily G}
    (h : O.SameComponentGeometry O') :
    O'.SameComponentGeometry O := by
  refine ⟨sameFixedPairingType_symm h.sameType, ?_, ?_⟩
  · intro P Q hP hQ hoverlap
    obtain ⟨v, hvP, hvQ⟩ := hoverlap
    exact (h.ac_eq_of_overlap hQ hP ⟨v, hvQ, hvP⟩).symm
  · intro P Q hP hQ hoverlap
    obtain ⟨v, hvP, hvQ⟩ := hoverlap
    exact (h.bd_eq_of_overlap hQ hP ⟨v, hvQ, hvP⟩).symm

/-- Distinct `(a,c)`-side components from compatible deformations are
disjoint. -/
theorem SameComponentGeometry.ac_disjoint_of_ne
    {O O' : FixedPairingPathFamily G}
    (h : O.SameComponentGeometry O')
    {P Q : Set V}
    (hP : P ∈ O.acPaths)
    (hQ : Q ∈ O'.acPaths)
    (hne : P ≠ Q) :
    Disjoint P Q := by
  refine Set.disjoint_left.mpr ?_
  intro v hvP hvQ
  exact hne (h.ac_eq_of_overlap hP hQ ⟨v, hvP, hvQ⟩)

/-- Distinct `(b,d)`-side components from compatible deformations are
disjoint. -/
theorem SameComponentGeometry.bd_disjoint_of_ne
    {O O' : FixedPairingPathFamily G}
    (h : O.SameComponentGeometry O')
    {P Q : Set V}
    (hP : P ∈ O.bdPaths)
    (hQ : Q ∈ O'.bdPaths)
    (hne : P ≠ Q) :
    Disjoint P Q := by
  refine Set.disjoint_left.mpr ?_
  intro v hvP hvQ
  exact hne (h.bd_eq_of_overlap hP hQ ⟨v, hvP, hvQ⟩)

/-- Two path components lie on the same side of the fixed pairing: either
both are `(a,c)` components or both are `(b,d)` components. -/
def SameComponentSide
    (O O' : FixedPairingPathFamily G)
    (P Q : Set V) : Prop :=
  (P ∈ O.acPaths ∧ Q ∈ O'.acPaths) ∨
    (P ∈ O.bdPaths ∧ Q ∈ O'.bdPaths)

/-- The component-disjointness step used near the start of the proof of
Corollary 11. -/
theorem SameComponentGeometry.disjoint_of_sameSide_of_ne
    {O O' : FixedPairingPathFamily G}
    (h : O.SameComponentGeometry O')
    {P Q : Set V}
    (hside : SameComponentSide O O' P Q)
    (hne : P ≠ Q) :
    Disjoint P Q := by
  rcases hside with hac | hbd
  · exact h.ac_disjoint_of_ne hac.1 hac.2 hne
  · exact h.bd_disjoint_of_ne hbd.1 hbd.2 hne

/-- Indexed-path form of cross-deformation component disjointness. -/
theorem SameComponentGeometry.pathRanges_disjoint_of_sameSide_of_ne
    {O O' : FixedPairingPathFamily G}
    (h : O.SameComponentGeometry O')
    {P Q : IndexedInducedPath G}
    (hside :
      SameComponentSide O O'
        (Set.range P.vertex) (Set.range Q.vertex))
    (hne : Set.range P.vertex ≠ Set.range Q.vertex) :
    Disjoint (Set.range P.vertex) (Set.range Q.vertex) :=
  h.disjoint_of_sameSide_of_ne hside hne

end FixedPairingPathFamily

end SimpleGraph
