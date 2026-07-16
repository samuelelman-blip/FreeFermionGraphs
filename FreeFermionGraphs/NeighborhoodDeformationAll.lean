import FreeFermionGraphs.NeighborhoodDeformation

/-!
# Full one-step neighborhood invariance

This module extends the external-vertex equivalence to every vertex, proving
that a single deformation preserves the entire open neighborhood of an even
hole.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- Every vertex of an alternating even-hole carrier belongs to the open
neighborhood of that carrier. -/
theorem mem_openNeighborhood_carrier_of_mem {k : Nat}
    (C : EvenHoleLabeling G k) {t : V} (ht : t ∈ C.carrier) :
    t ∈ G.openNeighborhood C.carrier := by
  rcases ht with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨C.b j, C.b_mem_carrier j, C.adj_a_b j⟩
  · exact ⟨C.a j, C.a_mem_carrier j, (C.adj_a_b j).symm⟩

/-- Every vertex in the union of the clone and original carrier neighbors
the original carrier. -/
theorem CloneAt.mem_openNeighborhood_carrier_of_mem_insert {k : Nat}
    {C : EvenHoleLabeling G k} {s t : V} {i : Fin k}
    (h : C.CloneAt s i) (ht : t ∈ Set.insert s C.carrier) :
    t ∈ G.openNeighborhood C.carrier := by
  rcases Set.mem_insert_iff.1 ht with rfl | htC
  · exact ⟨C.a i, C.a_mem_carrier i, h.adj_original⟩
  · exact C.mem_openNeighborhood_carrier_of_mem htC

/-- Every vertex in the union of the clone and original carrier also
neighbors the deformed carrier. -/
theorem CloneAt.mem_openNeighborhood_deformedCarrier_of_mem_insert
    {k : Nat} {C : EvenHoleLabeling G k} {s t : V} {i : Fin k}
    (h : C.CloneAt s i) (ht : t ∈ Set.insert s C.carrier) :
    t ∈ G.openNeighborhood (C.deformedCarrier s i) := by
  rcases Set.mem_insert_iff.1 ht with hts | htC
  · subst t
    exact ⟨C.b i, C.b_mem_deformedCarrier s i, h.adj_b⟩
  · rcases htC with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · by_cases hji : j = i
      · subst j
        exact ⟨s, C.clone_mem_deformedCarrier s i, h.adj_original.symm⟩
      · exact ⟨C.b j,
          C.mem_deformedCarrier_of_mem (C.b_mem_carrier j)
            (C.color_disjoint i j).symm,
          C.adj_a_b j⟩
    · by_cases hji : j = i
      · subst j
        exact ⟨s, C.clone_mem_deformedCarrier s i, h.adj_b.symm⟩
      · have haj_ne : C.a j ≠ C.a i := by
          intro haj
          exact hji (C.a_injective haj)
        exact ⟨C.a j,
          C.mem_deformedCarrier_of_mem (C.a_mem_carrier j) haj_ne,
          (C.adj_a_b j).symm⟩

/-- A single-vertex deformation preserves the open neighborhood of the
whole even-hole carrier.  This is the one-step form of Lemma 9. -/
theorem CloneAt.openNeighborhood_deformedCarrier_eq {k : Nat}
    {C : EvenHoleLabeling G k} {s : V} {i : Fin k}
    (h : C.CloneAt s i) (hclaw : G.IsClawFree) :
    G.openNeighborhood (C.deformedCarrier s i) =
      G.openNeighborhood C.carrier := by
  ext t
  by_cases ht : t ∈ Set.insert s C.carrier
  · constructor
    · intro _
      exact h.mem_openNeighborhood_carrier_of_mem_insert ht
    · intro _
      exact h.mem_openNeighborhood_deformedCarrier_of_mem_insert ht
  · exact h.external_openNeighborhood_deformedCarrier_iff hclaw ht

end EvenHoleLabeling

end SimpleGraph
