import FreeFermionGraphs.Lemma11PathCounts

/-!
# Lemma 11(a): dependent anticommuting step

This module assembles the local ingredients of Lemma 11(a).  For a vertex
in a dependent subset whose term anticommutes with the active induced path,
we obtain the restricted path-neighbor count, the degree increase, and the
common-neighbor witness supplied by the deformation geometry.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- A dependent vertex is distinct from the vertex introduced at its
deformation step. -/
theorem dependentVertex_ne_introduced
    {Cprime : Set V} {introduced removed u : V}
    (hu : u ∈ G.dependentSubset Cprime introduced removed) :
    u ≠ introduced := by
  intro hui
  subst u
  exact (G.loopless.irrefl introduced) hu.2.1

/-- The dependent-membership direction of Lemma 11(a), at one deformation
step. -/
theorem lemma11a_dependent_step
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
      ∃ v ∈ Set.range C.vertex,
        G.Adj u v ∧
        G.Adj introduced v ∧
        G.Adj (C.vertex i) v := by
  refine ⟨G.dependentVertex_ne_introduced huDependent, ?_, ?_, ?_⟩
  · exact P.anticommutesWith_count_eq_one_or_three
      hclaw huOutsidePath hanti
  · exact hdeform.dependent_externalDegree_deform_eq_add_one
      huDependent
  · exact dependentSubset_has_common_hole_neighbor
      hdeform hclaw huDependent huOutsideHole

end SimpleGraph
