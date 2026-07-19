import FreeFermionGraphs.Lemma11BConsolidatedDescent

/-!
# External-neighbor sets of indexed holes

The paper's in-path branch of Lemma 11(b) compares neighborhoods as sets of
vertices, even when successive indexed-hole presentations use different
index types. This module supplies that carrier-level interface.

The image of the neighbor-index set under an injective hole labeling has
the same cardinality as the index set. Consequently external degree depends
only on the carrier of an indexed hole, not on its particular indexing.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- Hole vertices adjacent to `u`, represented in the ambient vertex
type rather than by hole indices. -/
def externalNeighborSet
    (C : IndexedInducedHole G) (u : V) : Set V :=
  C.vertex '' C.neighborIndexSet u

@[simp]
theorem mem_externalNeighborSet
    (C : IndexedInducedHole G) {u v : V} :
    v ∈ C.externalNeighborSet u ↔
      v ∈ Set.range C.vertex ∧ G.Adj u v := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, rfl⟩, hi⟩
  · rintro ⟨⟨i, rfl⟩, hi⟩
    exact ⟨i, hi, rfl⟩

/-- Passing from neighbor indices to their labeled vertices preserves
cardinality. -/
theorem externalNeighborSet_ncard
    (C : IndexedInducedHole G) (u : V) :
    (C.externalNeighborSet u).ncard = C.externalDegree u := by
  unfold externalNeighborSet externalDegree
  exact Set.ncard_image_of_injective _ C.injective

/-- Equal hole carriers have equal ambient external-neighbor sets. -/
theorem externalNeighborSet_eq_of_range_eq
    (C D : IndexedInducedHole G)
    {u : V}
    (hcarrier : Set.range C.vertex = Set.range D.vertex) :
    C.externalNeighborSet u = D.externalNeighborSet u := by
  ext v
  simp only [mem_externalNeighborSet]
  rw [hcarrier]

/-- External degree is invariant under changing the indexed presentation
of the same hole carrier. -/
theorem externalDegree_eq_of_range_eq
    (C D : IndexedInducedHole G)
    {u : V}
    (hcarrier : Set.range C.vertex = Set.range D.vertex) :
    C.externalDegree u = D.externalDegree u := by
  calc
    C.externalDegree u = (C.externalNeighborSet u).ncard :=
      (C.externalNeighborSet_ncard u).symm
    _ = (D.externalNeighborSet u).ncard := by
      rw [C.externalNeighborSet_eq_of_range_eq D hcarrier]
    _ = D.externalDegree u :=
      D.externalNeighborSet_ncard u

end IndexedInducedHole

namespace FixedPairingPathFamily

namespace ConcreteDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Consecutive concrete deformation steps agree on external degree at the
intermediate carrier. -/
theorem degreeAfter_eq_nextDegreeBefore
    (D : ConcreteDeformation O Cprime)
    {i j : Fin D.stepCount}
    (hij : i.val + 1 = j.val)
    (u : V) :
    (D.step i).degreeAfter u =
      (D.step j).degreeBefore u := by
  unfold ConcreteDeformationStep.degreeAfter
    ConcreteDeformationStep.degreeBefore
  exact
    IndexedInducedHole.externalDegree_eq_of_range_eq
      (D.step i).after (D.step j).before
      (D.carrier_chain hij)

end ConcreteDeformation

end FixedPairingPathFamily

end SimpleGraph
