import FreeFermionGraphs.Lemma11BExternalNeighborSets

/-!
# Degree of a vertex on an indexed hole

Every vertex of an indexed induced hole has exactly its predecessor and
successor as hole neighbors. This elementary fact is the starting value
`Δ = 2` in the in-path branch of Lemma 11(b).

The proof treats the first, last, and interior cyclic indices explicitly.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- A hole vertex has external degree two when counted against its own
indexed hole. -/
theorem externalDegree_vertex_eq_two
    (C : IndexedInducedHole G)
    (i : Fin C.card) :
    C.externalDegree (C.vertex i) = 2 := by
  unfold externalDegree
  apply Set.ncard_eq_two.mpr
  have hcard : 4 ≤ C.card := C.four_le_card
  have hi : i.val < C.card := i.isLt
  by_cases hfirst : i.val = 0
  · let p : Fin C.card := ⟨1, by omega⟩
    let q : Fin C.card := ⟨C.card - 1, by omega⟩
    have hpq : p ≠ q := by
      intro hpq
      have hval := congrArg Fin.val hpq
      dsimp [p, q] at hval
      omega
    refine ⟨p, q, hpq, ?_⟩
    ext x
    simp only [mem_neighborIndexSet,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [C.adj_iff]
    constructor
    · intro hx
      rcases hx with hx | hx | hx | hx
      · left
        apply Fin.ext
        dsimp [p]
        omega
      · omega
      · right
        apply Fin.ext
        dsimp [q]
        omega
      · omega
    · intro hx
      rcases hx with rfl | rfl
      · exact Or.inl (by
          dsimp [p]
          omega)
      · exact Or.inr (Or.inr (Or.inl ⟨hfirst, by
          dsimp [q]
          omega⟩)))
  · by_cases hlast : i.val + 1 = C.card
    · let p : Fin C.card := ⟨0, by omega⟩
      let q : Fin C.card := ⟨C.card - 2, by omega⟩
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [p, q] at hval
        omega
      refine ⟨p, q, hpq, ?_⟩
      ext x
      simp only [mem_neighborIndexSet,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [C.adj_iff]
      constructor
      · intro hx
        rcases hx with hx | hx | hx | hx
        · omega
        · right
          apply Fin.ext
          dsimp [q]
          omega
        · omega
        · left
          apply Fin.ext
          dsimp [p]
          omega
      · intro hx
        rcases hx with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr ⟨by rfl, hlast⟩))
        · exact Or.inr (Or.inl (by
            dsimp [q]
            omega))
    · let p : Fin C.card := ⟨i.val - 1, by omega⟩
      let q : Fin C.card := ⟨i.val + 1, by omega⟩
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [p, q] at hval
        omega
      refine ⟨p, q, hpq, ?_⟩
      ext x
      simp only [mem_neighborIndexSet,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [C.adj_iff]
      constructor
      · intro hx
        rcases hx with hx | hx | hx | hx
        · right
          apply Fin.ext
          dsimp [q]
          omega
        · left
          apply Fin.ext
          dsimp [p]
          omega
        · omega
        · omega
      · intro hx
        rcases hx with rfl | rfl
        · exact Or.inr (Or.inl (by
            dsimp [p]
            omega))
        · exact Or.inl (by
            dsimp [q])

end IndexedInducedHole

end SimpleGraph
