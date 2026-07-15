import FreeFermionGraphs.Corollaries23

/-!
# Single-vertex deformations

The graph-theoretic operation from Definition 10 of the paper.  Replacing a
vertex of an indexed induced hole by a clone preserves the indexed induced
hole, with the same cyclic order.  This is the structural input used in the
proof of Lemma 8.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- A vertex `s` is a clone of the vertex at index `i` in `C` when it lies
outside `C` and its neighbors in `C` are exactly the vertex at `i` together
with the two cycle neighbors of that vertex.

This is the indexed-hole version of the paper's notation `s ≺_C C.vertex i`.
The right-hand side uses adjacency in the induced hole to avoid choosing
predecessor and successor indices explicitly. -/
structure IndexedInducedHole.SingleVertexDeformation
    (C : IndexedInducedHole G) (s : V) (i : Fin C.card) : Prop where
  outside : s ∉ Set.range C.vertex
  adj_iff : ∀ q : Fin C.card,
    G.Adj s (C.vertex q) ↔
      q = i ∨ G.Adj (C.vertex i) (C.vertex q)

namespace IndexedInducedHole

/-- Replace the vertex at index `i` by `s`, retaining all other indexed
vertices. -/
def replaceVertex (C : IndexedInducedHole G) (s : V) (i : Fin C.card) :
    Fin C.card → V :=
  fun q => if q = i then s else C.vertex q

@[simp]
theorem replaceVertex_at (C : IndexedInducedHole G) (s : V)
    (i : Fin C.card) : C.replaceVertex s i i = s := by
  simp [replaceVertex]

@[simp]
theorem replaceVertex_away (C : IndexedInducedHole G) (s : V)
    {i q : Fin C.card} (hqi : q ≠ i) :
    C.replaceVertex s i q = C.vertex q := by
  simp [replaceVertex, hqi]

/-- A clone is adjacent to the vertex that it replaces. -/
theorem SingleVertexDeformation.adj_clone
    {C : IndexedInducedHole G} {s : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i) :
    G.Adj s (C.vertex i) := by
  exact (h.adj_iff i).2 (Or.inl rfl)

/-- A clone is adjacent to each cycle neighbor of the vertex it replaces. -/
theorem SingleVertexDeformation.adj_of_clone_adj
    {C : IndexedInducedHole G} {s : V} {i q : Fin C.card}
    (h : C.SingleVertexDeformation s i)
    (hiq : G.Adj (C.vertex i) (C.vertex q)) :
    G.Adj s (C.vertex q) := by
  exact (h.adj_iff q).2 (Or.inr hiq)

/-- Away from the replaced vertex, a clone and its original have exactly
the same neighbors on the hole. -/
theorem SingleVertexDeformation.adj_iff_clone_adj
    {C : IndexedInducedHole G} {s : V} {i q : Fin C.card}
    (h : C.SingleVertexDeformation s i) (hqi : q ≠ i) :
    G.Adj s (C.vertex q) ↔ G.Adj (C.vertex i) (C.vertex q) := by
  rw [h.adj_iff q]
  simp [hqi]

/-- The first forced-neighbor step in Lemma 8.  If `t` lies outside the
original hole and its clone, and is adjacent to exactly one of the clone and
the replaced vertex, then `t` is adjacent to one of the two cycle neighbors
of the replaced vertex. -/
theorem SingleVertexDeformation.dependent_hits_cycle_neighbor
    {C : IndexedInducedHole G} {s t : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i) (hclaw : G.IsClawFree)
    (htC : t ∉ Set.insert s (Set.range C.vertex))
    (hexact :
      (G.Adj t s ∧ ¬G.Adj t (C.vertex i)) ∨
      (¬G.Adj t s ∧ G.Adj t (C.vertex i))) :
    ∃ q : Fin C.card,
      G.Adj (C.vertex i) (C.vertex q) ∧ G.Adj t (C.vertex q) := by
  rcases hexact with ⟨hts, _hti⟩ | ⟨_hts, hti⟩
  · obtain ⟨p, q, hpq, hip, hiq, hpq_nonadj⟩ :=
      C.exists_two_nonadjacent_neighbors i
    have hsp : G.Adj s (C.vertex p) := h.adj_of_clone_adj hip
    have hsq : G.Adj s (C.vertex q) := h.adj_of_clone_adj hiq
    have htp : t ≠ C.vertex p := by
      intro htp
      exact htC (Set.mem_insert_iff.2
        (Or.inr ⟨p, htp.symm⟩))
    have htq : t ≠ C.vertex q := by
      intro htq
      exact htC (Set.mem_insert_iff.2
        (Or.inr ⟨q, htq.symm⟩))
    have hpq_vertices : C.vertex p ≠ C.vertex q := by
      intro hpqv
      exact hpq (C.injective hpqv)
    rcases hclaw.adjacent_to_one_of_nonadjacent_neighbors
        hts hsp hsq htp htq hpq_vertices hpq_nonadj with htp' | htq'
    · exact ⟨p, hip, htp'⟩
    · exact ⟨q, hiq, htq'⟩
  · have ht_range : t ∉ Set.range C.vertex := by
      intro ht
      exact htC (Set.mem_insert_iff.2 (Or.inr ht))
    exact C.corollary2 hclaw ht_range hti

/-- Replacing a hole vertex by a clone produces another indexed induced
hole with the same cardinality and cyclic indexing. -/
def deform (C : IndexedInducedHole G) {s : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i) : IndexedInducedHole G where
  card := C.card
  four_le_card := C.four_le_card
  vertex := C.replaceVertex s i
  injective := by
    intro p q hpq
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · exact hq.symm
      · have hsq : s = C.vertex q := by
          simpa [replaceVertex, hq] using hpq
        exact (h.outside ⟨q, hsq.symm⟩).elim
    · by_cases hq : q = i
      · subst q
        have hps : C.vertex p = s := by
          simpa [replaceVertex, hp] using hpq
        exact (h.outside ⟨p, hps⟩).elim
      · exact C.injective (by
          simpa [replaceVertex, hp, hq] using hpq)
  adj_iff := by
    intro p q
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · subst q
        have hcyc : ¬CyclicAdjacent i i := by
          unfold CyclicAdjacent
          have hi := i.isLt
          have hcard := C.four_le_card
          omega
        apply iff_of_false
        · simpa [replaceVertex] using G.loopless.irrefl s
        · exact hcyc
      · simp only [replaceVertex, if_pos, if_neg hq]
        rw [h.adj_iff q, C.adj_iff i q]
        simp [hq]
    · by_cases hq : q = i
      · subst q
        simp only [replaceVertex, if_neg hp, if_pos]
        have hs : G.Adj s (C.vertex p) ↔ CyclicAdjacent i p := by
          rw [h.adj_iff p, C.adj_iff i p]
          simp [hp]
        constructor
        · intro hps
          exact CyclicAdjacent.symm (hs.1 hps.symm)
        · intro hpi
          exact (hs.2 (CyclicAdjacent.symm hpi)).symm
      · simp only [replaceVertex, if_neg hp, if_neg hq]
        exact C.adj_iff p q

@[simp]
theorem deform_card (C : IndexedInducedHole G) {s : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation s i) :
    (C.deform h).card = C.card :=
  rfl

@[simp]
theorem deform_vertex_at (C : IndexedInducedHole G) {s : V}
    {i : Fin C.card} (h : C.SingleVertexDeformation s i) :
    (C.deform h).vertex i = s := by
  simp [deform]

@[simp]
theorem deform_vertex_away (C : IndexedInducedHole G) {s : V}
    {i q : Fin C.card} (h : C.SingleVertexDeformation s i) (hqi : q ≠ i) :
    (C.deform h).vertex q = C.vertex q := by
  simp [deform, hqi]

end IndexedInducedHole

end SimpleGraph
