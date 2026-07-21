import FreeFermionGraphs.Lemma11AParity
import FreeFermionGraphs.Lemma11BHoleVertexDegree

/-!
# Lemma 11(a): odd external degree on an even hole

Lemma 7 leaves only degree three as an odd external degree on an even
induced hole.  This is the final numerical step in the original-hole part
of Lemma 11(a.ii).
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- An external vertex of an even induced hole with odd external degree
has exactly three hole neighbors. -/
theorem externalDegree_eq_three_of_even_and_odd
    (C : IndexedInducedHole G)
    (hclaw : G.IsClawFree)
    {u : V}
    (huOutside : u ∉ Set.range C.vertex)
    (hEven : Even C.card)
    (hOdd : C.externalDegree u % 2 = 1) :
    C.externalDegree u = 3 := by
  rcases C.lemma7 hclaw huOutside with hzero | htwo | hthree | hfour | hfive
  · change (C.neighborIndexSet u).ncard % 2 = 1 at hOdd
    rw [hzero] at hOdd
    omega
  · change (C.neighborIndexSet u).ncard % 2 = 1 at hOdd
    rw [htwo.1] at hOdd
    omega
  · exact hthree.1
  · change (C.neighborIndexSet u).ncard % 2 = 1 at hOdd
    rw [hfour.1] at hOdd
    omega
  · have hcard : C.card = 5 := hfive.2
    rcases hEven with ⟨k, hk⟩
    omega

/-- Odd degree already implies that the vertex is external to the hole:
every vertex on an induced hole has degree two in that hole.  This removes
the redundant externality hypotheses from the global part of Lemma 11(a). -/
theorem externalDegree_eq_three_of_even_and_odd_any
    (C : IndexedInducedHole G)
    (hclaw : G.IsClawFree)
    {u : V}
    (hEven : Even C.card)
    (hOdd : C.externalDegree u % 2 = 1) :
    C.externalDegree u = 3 := by
  have huOutside : u ∉ Set.range C.vertex := by
    rintro ⟨i, rfl⟩
    have htwo := C.externalDegree_vertex_eq_two i
    rw [htwo] at hOdd
    omega
  exact C.externalDegree_eq_three_of_even_and_odd
    hclaw huOutside hEven hOdd

end IndexedInducedHole

end SimpleGraph
