import FreeFermionGraphs.Lemma11A

/-!
# Lemma 11(a): persistent common neighbor

The common neighbor produced at a dependent deformation step is adjacent to
the removed hole vertex, so it cannot be that removed vertex.  It therefore
survives the replacement and belongs to both the pre- and post-deformation
hole carriers, as used in Lemma 11(a.i).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- A vertex of the old hole adjacent to the removed vertex survives the
single-vertex deformation. -/
theorem SingleVertexDeformation.mem_range_deform_of_mem_range_of_adj_original
    {C : IndexedInducedHole G} {introduced v : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hvC : v ∈ Set.range C.vertex)
    (hiv : G.Adj (C.vertex i) v) :
    v ∈ Set.range (C.deform h).vertex := by
  rcases hvC with ⟨q, rfl⟩
  have hqi : q ≠ i := by
    intro hqi
    subst q
    exact (G.loopless.irrefl (C.vertex i)) hiv
  exact ⟨q, by simp [hqi]⟩

/-- The dependent common neighbor belongs to both holes. -/
theorem SingleVertexDeformation.dependent_common_neighbor_persists
    {C : IndexedInducedHole G} {Cprime : Set V}
    {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hclaw : G.IsClawFree)
    (hu : u ∈ G.dependentSubset Cprime introduced (C.vertex i))
    (huOutside : u ∉ Set.insert introduced (Set.range C.vertex)) :
    ∃ v,
      v ∈ Set.range C.vertex ∧
      v ∈ Set.range (C.deform h).vertex ∧
      G.Adj u v ∧
      G.Adj introduced v ∧
      G.Adj (C.vertex i) v := by
  obtain ⟨v, hvC, huv, hintroducedv, hremovedv⟩ :=
    dependentSubset_has_common_hole_neighbor
      h hclaw hu huOutside
  exact ⟨v, hvC,
    h.mem_range_deform_of_mem_range_of_adj_original hvC hremovedv,
    huv, hintroducedv, hremovedv⟩

end IndexedInducedHole

/-- Lemma 11(a)'s dependent-step package with the common witness retained in
both the old and new holes. -/
theorem lemma11a_dependent_step_persistent
    (P : IndexedInducedPath G)
    (C : IndexedInducedHole G)
    (hclaw : G.IsClawFree)
    {Cprime : Set V} {introduced u : V} {i : Fin C.card}
    (hdeform : C.SingleVertexDeformation introduced i)
    (huDependent :
      u ∈ G.dependentSubset Cprime introduced (C.vertex i))
    (huOutsidePath : u ∉ Set.range P.vertex)
    (huOutsideHole :
      u ∉ Set.insert introduced (Set.range C.vertex))
    (hanti : P.AnticommutesWith u) :
    u ≠ introduced ∧
      ((P.neighborIndexSet u).ncard = 1 ∨
        (P.neighborIndexSet u).ncard = 3) ∧
      (C.deform hdeform).externalDegree u =
        C.externalDegree u + 1 ∧
      ∃ v,
        v ∈ Set.range C.vertex ∧
        v ∈ Set.range (C.deform hdeform).vertex ∧
        G.Adj u v ∧
        G.Adj introduced v ∧
        G.Adj (C.vertex i) v := by
  obtain ⟨hne, hcount, hdegree, v, hvC,
      huv, hintroducedv, hremovedv⟩ :=
    lemma11a_dependent_step P C hclaw hdeform huDependent
      huOutsidePath huOutsideHole hanti
  exact ⟨hne, hcount, hdegree, v, hvC,
    hdeform.mem_range_deform_of_mem_range_of_adj_original
      hvC hremovedv,
    huv, hintroducedv, hremovedv⟩

end SimpleGraph
