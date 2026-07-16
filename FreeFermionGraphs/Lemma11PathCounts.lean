import FreeFermionGraphs.PathCommutation

/-!
# Lemma 11: path neighbor counts

This file connects the carrier-level parity definition of path commutation
to the indexed neighbor sets classified by Lemma 7.  An external vertex
anticommuting with an induced path has exactly one or three path neighbors;
a commuting external vertex has zero, two, or four.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedPath

/-- The adjacent vertices in a path carrier are the image of its adjacent
indices. -/
theorem adjacentIn_range_eq_image
    (P : IndexedInducedPath G) (u : V) :
    G.adjacentIn u (Set.range P.vertex) =
      P.vertex '' P.neighborIndexSet u := by
  ext v
  constructor
  · rintro ⟨⟨i, hiv⟩, huv⟩
    subst v
    exact ⟨i, huv, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, rfl⟩, hi⟩

/-- Counting adjacent carrier vertices agrees with counting adjacent path
indices because the path labeling is injective. -/
theorem adjacencyCount_range_eq_neighborIndexSet_ncard
    (P : IndexedInducedPath G) (u : V) :
    G.adjacencyCount u (Set.range P.vertex) =
      (P.neighborIndexSet u).ncard := by
  change (G.adjacentIn u (Set.range P.vertex)).ncard =
    (P.neighborIndexSet u).ncard
  rw [P.adjacentIn_range_eq_image]
  exact (P.injective.injOn).ncard_image

theorem commutesWith_iff_neighborIndexSet_mod_eq_zero
    (P : IndexedInducedPath G) (u : V) :
    P.CommutesWith u ↔ (P.neighborIndexSet u).ncard % 2 = 0 := by
  change G.adjacencyCount u (Set.range P.vertex) % 2 = 0 ↔
    (P.neighborIndexSet u).ncard % 2 = 0
  rw [P.adjacencyCount_range_eq_neighborIndexSet_ncard]

theorem anticommutesWith_iff_neighborIndexSet_mod_eq_one
    (P : IndexedInducedPath G) (u : V) :
    P.AnticommutesWith u ↔ (P.neighborIndexSet u).ncard % 2 = 1 := by
  change G.adjacencyCount u (Set.range P.vertex) % 2 = 1 ↔
    (P.neighborIndexSet u).ncard % 2 = 1
  rw [P.adjacencyCount_range_eq_neighborIndexSet_ncard]

/-- Under Lemma 7, anticommutation leaves exactly the one- and
three-neighbor path cases. -/
theorem anticommutesWith_count_eq_one_or_three
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {u : V}
    (huOutside : u ∉ Set.range P.vertex)
    (hanti : P.AnticommutesWith u) :
    (P.neighborIndexSet u).ncard = 1 ∨
      (P.neighborIndexSet u).ncard = 3 := by
  have hodd :
      (P.neighborIndexSet u).ncard % 2 = 1 :=
    (P.anticommutesWith_iff_neighborIndexSet_mod_eq_one u).1 hanti
  rcases P.lemma7 hclaw huOutside with
    hzero | hone | htwo | hthree | hfour
  · omega
  · exact Or.inl hone.1
  · omega
  · exact Or.inr hthree.1
  · omega

/-- Under Lemma 7, commutation leaves exactly the zero-, two-, and
four-neighbor path cases. -/
theorem commutesWith_count_eq_zero_or_two_or_four
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {u : V}
    (huOutside : u ∉ Set.range P.vertex)
    (hcomm : P.CommutesWith u) :
    (P.neighborIndexSet u).ncard = 0 ∨
      (P.neighborIndexSet u).ncard = 2 ∨
      (P.neighborIndexSet u).ncard = 4 := by
  have heven :
      (P.neighborIndexSet u).ncard % 2 = 0 :=
    (P.commutesWith_iff_neighborIndexSet_mod_eq_zero u).1 hcomm
  rcases P.lemma7 hclaw huOutside with
    hzero | hone | htwo | hthree | hfour
  · exact Or.inl hzero
  · omega
  · exact Or.inr (Or.inl htwo.1)
  · omega
  · exact Or.inr (Or.inr hfour.1)

end IndexedInducedPath

end SimpleGraph
