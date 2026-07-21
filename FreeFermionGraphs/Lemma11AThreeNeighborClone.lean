import FreeFermionGraphs.Lemma7
import FreeFermionGraphs.Lemma11Degree
import FreeFermionGraphs.Deformation

/-!
# Lemma 11(a): three hole neighbors give a clone

The degree-three case of Lemma 7 says that the three neighbors of an
external vertex on an induced hole form an induced path.  The middle vertex
of that path has exactly those two cycle neighbors, so the external vertex
is a clone of it.  This is the graph-theoretic part of the notation
`u ≺_C v` used in Lemma 11(a)(ii).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- A hole vertex has no third distinct neighbor. -/
theorem adjacent_index_eq_of_two_distinct_neighbors
    (C : IndexedInducedHole G) {i a b k : Fin C.card}
    (hab : a ≠ b)
    (hia : G.Adj (C.vertex i) (C.vertex a))
    (hib : G.Adj (C.vertex i) (C.vertex b))
    (hik : G.Adj (C.vertex i) (C.vertex k)) :
    k = a ∨ k = b := by
  have hcard := C.four_le_card
  have hi := i.isLt
  have ha := a.isLt
  have hb := b.isLt
  have hk := k.isLt
  have habVal : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  have hia' := (C.adj_iff i a).mp hia
  have hib' := (C.adj_iff i b).mp hib
  have hik' := (C.adj_iff i k).mp hik
  unfold CyclicAdjacent at hia' hib' hik'
  by_cases hka : k = a
  · exact Or.inl hka
  · right
    apply Fin.ext
    have hkaVal : k.val ≠ a.val := by
      intro h
      exact hka (Fin.ext h)
    rcases hia' with hia' | hia' | hia' | hia' <;>
      rcases hib' with hib' | hib' | hib' | hib' <;>
      rcases hik' with hik' | hik' | hik' | hik' <;> omega

/-- An external vertex with exactly three hole neighbors is a clone of the
middle vertex of their induced path. -/
theorem exists_singleVertexDeformation_of_externalDegree_eq_three
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {u : V}
    (huOutside : u ∉ Set.range C.vertex)
    (hthree : C.externalDegree u = 3) :
    ∃ q : Fin C.card, C.SingleVertexDeformation u q := by
  classical
  change (C.neighborIndexSet u).ncard = 3 at hthree
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ :=
    Set.ncard_eq_three.mp hthree
  have hp : G.Adj u (C.vertex p) := by
    change p ∈ C.neighborIndexSet u
    rw [hset]
    simp
  have hq : G.Adj u (C.vertex q) := by
    change q ∈ C.neighborIndexSet u
    rw [hset]
    simp
  have hr : G.Adj u (C.vertex r) := by
    change r ∈ C.neighborIndexSet u
    rw [hset]
    simp
  have hexact : ∀ k : Fin C.card, G.Adj u (C.vertex k) →
      k = p ∨ k = q ∨ k = r := by
    intro k hk
    change k ∈ C.neighborIndexSet u at hk
    rw [hset] at hk
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hk
  have hshape := C.three_external_neighbors_induce_path
    hclaw huOutside hpq hpr hqr hp hq hr hexact
  have clone_of_path
      (left center right : Fin C.card)
      (hleft : G.Adj u (C.vertex left))
      (hcenter : G.Adj u (C.vertex center))
      (hright : G.Adj u (C.vertex right))
      (hpath : G.IsInducedPathTriple
        (C.vertex left) (C.vertex center) (C.vertex right))
      (hexact' : ∀ k : Fin C.card, G.Adj u (C.vertex k) →
        k = left ∨ k = center ∨ k = right) :
      C.SingleVertexDeformation u center := by
    have hleftRight : left ≠ right := by
      intro h
      apply hpath.2.2.2
      simp [h]
    refine ⟨huOutside, ?_⟩
    intro k
    constructor
    · intro huk
      rcases hexact' k huk with hkl | hkc | hkr
      · subst k
        exact Or.inr hpath.1.symm
      · exact Or.inl hkc
      · subst k
        exact Or.inr hpath.2.1
    · rintro (hkc | hck)
      · subst k
        exact hcenter
      · rcases C.adjacent_index_eq_of_two_distinct_neighbors
          hleftRight hpath.1.symm hpath.2.1 hck with hkl | hkr
        · subst k
          exact hleft
        · subst k
          exact hright
  rcases hshape with hpMiddle | hqMiddle | hrMiddle
  · refine ⟨p, clone_of_path q p r hq hp hr hpMiddle ?_⟩
    intro k hk
    rcases hexact k hk with hkp | hkq | hkr
    · exact Or.inr (Or.inl hkp)
    · exact Or.inl hkq
    · exact Or.inr (Or.inr hkr)
  · refine ⟨q, clone_of_path p q r hp hq hr hqMiddle ?_⟩
    exact hexact
  · refine ⟨r, clone_of_path p r q hp hr hq hrMiddle ?_⟩
    intro k hk
    rcases hexact k hk with hkp | hkq | hkr
    · exact Or.inl hkp
    · exact Or.inr (Or.inr hkq)
    · exact Or.inr (Or.inl hkr)

end IndexedInducedHole

end SimpleGraph
