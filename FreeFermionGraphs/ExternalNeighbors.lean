import FreeFermionGraphs.InducedStructures

/-!
# External neighbors of induced paths and holes

The first cardinality cases in the neighboring-relation classification of
Lemma 7.  An external vertex may have a unique neighbor on an induced path
only at an endpoint, while it cannot have a unique neighbor on a hole.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Indices of the vertices of `P` adjacent to `j`. -/
def IndexedInducedPath.neighborIndexSet
    (P : IndexedInducedPath G) (j : V) : Set (Fin P.card) :=
  {i | G.Adj j (P.vertex i)}

/-- Indices of the vertices of `C` adjacent to `j`. -/
def IndexedInducedHole.neighborIndexSet
    (C : IndexedInducedHole G) (j : V) : Set (Fin C.card) :=
  {i | G.Adj j (C.vertex i)}

@[simp]
theorem IndexedInducedPath.mem_neighborIndexSet
    (P : IndexedInducedPath G) (j : V) (i : Fin P.card) :
    i ∈ P.neighborIndexSet j ↔ G.Adj j (P.vertex i) :=
  Iff.rfl

@[simp]
theorem IndexedInducedHole.mem_neighborIndexSet
    (C : IndexedInducedHole G) (j : V) (i : Fin C.card) :
    i ∈ C.neighborIndexSet j ↔ G.Adj j (C.vertex i) :=
  Iff.rfl

/-- Case (b.iii) of Lemma 7: if an external vertex has a unique neighbor on
an indexed induced path, that neighbor is one of the two endpoints. -/
theorem IndexedInducedPath.unique_external_neighbor_is_endpoint
    (P : IndexedInducedPath G) (hclaw : G.IsClawFree) {j : V}
    (hjP : j ∉ Set.range P.vertex) {i : Fin P.card}
    (hji : G.Adj j (P.vertex i))
    (hunique : ∀ k : Fin P.card, G.Adj j (P.vertex k) → k = i) :
    i.val = 0 ∨ i.val + 1 = P.card := by
  by_contra hendpoint
  have hfirst : i.val ≠ 0 := by
    intro h
    exact hendpoint (Or.inl h)
  have hlast : i.val + 1 ≠ P.card := by
    intro h
    exact hendpoint (Or.inr h)
  have hi : i.val < P.card := i.isLt
  let p : Fin P.card := ⟨i.val - 1, by omega⟩
  let q : Fin P.card := ⟨i.val + 1, by omega⟩
  have hip : G.Adj (P.vertex i) (P.vertex p) := by
    apply (P.adj_iff i p).2
    right
    dsimp [p]
    omega
  have hiq : G.Adj (P.vertex i) (P.vertex q) := by
    apply (P.adj_iff i q).2
    left
    rfl
  have hpq : p ≠ q := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [p, q] at hval
    omega
  have hpq_vertices : P.vertex p ≠ P.vertex q := by
    intro h
    exact hpq (P.injective h)
  have hpq_nonadj : ¬G.Adj (P.vertex p) (P.vertex q) := by
    intro h
    rcases (P.adj_iff p q).1 h with h | h
    · dsimp [p, q] at h
      omega
    · dsimp [p, q] at h
      omega
  have hjp : j ≠ P.vertex p := by
    intro h
    exact hjP ⟨p, h.symm⟩
  have hjq : j ≠ P.vertex q := by
    intro h
    exact hjP ⟨q, h.symm⟩
  have hjp_nonadj : ¬G.Adj j (P.vertex p) := by
    intro h
    have hpi := hunique p h
    have hval := congrArg Fin.val hpi
    dsimp [p] at hval
    omega
  have hjq_nonadj : ¬G.Adj j (P.vertex q) := by
    intro h
    have hqi := hunique q h
    have hval := congrArg Fin.val hqi
    dsimp [q] at hval
    omega
  rcases hclaw hji.symm hip hiq hjp hjq hpq_vertices with
    hjp_adj | hjq_adj | hpq_adj
  · exact hjp_nonadj hjp_adj
  · exact hjq_nonadj hjq_adj
  · exact hpq_nonadj hpq_adj

/-- Every external vertex adjacent to a hole has a second, differently
indexed neighbor on that hole. -/
theorem IndexedInducedHole.exists_second_external_neighbor
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) (i : Fin C.card)
    (hji : G.Adj j (C.vertex i)) :
    ∃ k : Fin C.card, k ≠ i ∧ G.Adj j (C.vertex k) := by
  obtain ⟨p, q, hpq, hip, hiq, hpq_nonadj, hj⟩ :=
    C.external_neighbor_hits_cycle_neighbor hclaw hjC i hji
  rcases hj with hjp | hjq
  · refine ⟨p, ?_, hjp⟩
    intro h
    subst p
    exact hip.ne rfl
  · refine ⟨q, ?_, hjq⟩
    intro h
    subst q
    exact hiq.ne rfl

/-- The one-neighbor case of Lemma 7 is impossible for holes. -/
theorem IndexedInducedHole.not_unique_external_neighbor
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) (i : Fin C.card)
    (hji : G.Adj j (C.vertex i)) :
    ¬(∀ k : Fin C.card, G.Adj j (C.vertex k) → k = i) := by
  intro hunique
  obtain ⟨k, hki, hjk⟩ := C.exists_second_external_neighbor hclaw hjC i hji
  exact hki (hunique k hjk)

end SimpleGraph
