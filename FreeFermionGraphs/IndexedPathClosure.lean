import FreeFermionGraphs.CliqueRootedPathOriginalTail

/-!
# Closing an induced path into an induced hole

The root-endpoint form of the manuscript's exceptional three-neighbour case
becomes a hole after the artificial root is removed.  This module supplies
the general graph constructor: append a fresh vertex adjacent exactly to the
two endpoints of an induced path of at least three vertices.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- Exact data for closing `P` with a fresh vertex. -/
structure EndpointClosureData
    (P : IndexedInducedPath G) (s : V) : Prop where
  three_le : 3 ≤ P.card
  outside : s ∉ Set.range P.vertex
  adj_iff : ∀ q : Fin P.card,
    G.Adj s (P.vertex q) ↔ q.val = 0 ∨ q.val + 1 = P.card

/-- Append the closing vertex after the path order, obtaining the cyclic
order on the resulting induced hole. -/
def closeToHole
    (P : IndexedInducedPath G) {s : V}
    (h : P.EndpointClosureData s) : IndexedInducedHole G where
  card := P.card + 1
  four_le_card := by
    have := h.three_le
    omega
  vertex := Fin.lastCases s P.vertex
  injective := by
    intro p
    refine Fin.lastCases ?_ (fun p => ?_) p
    · intro q
      refine Fin.lastCases ?_ (fun q => ?_) q
      · intro _
        rfl
      · intro hsq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hsq
        exact (h.outside ⟨q, hsq.symm⟩).elim
    · intro q
      refine Fin.lastCases ?_ (fun q => ?_) q
      · intro hps
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hps
        exact (h.outside ⟨p, hps⟩).elim
      · intro hpq
        simp only [Fin.lastCases_castSucc] at hpq
        exact congrArg Fin.castSucc (P.injective hpq)
  adj_iff := by
    intro p
    refine Fin.lastCases ?_ (fun p => ?_) p
    · intro q
      refine Fin.lastCases ?_ (fun q => ?_) q
      · simp only [Fin.lastCases_last]
        constructor
        · intro hadj
          exact (G.irrefl hadj).elim
        · intro hcyc
          unfold CyclicAdjacent at hcyc
          simp only [Fin.val_last] at hcyc
          have := h.three_le
          omega
      · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        rw [h.adj_iff q]
        unfold CyclicAdjacent
        simp only [Fin.val_last, Fin.val_castSucc]
        have := h.three_le
        constructor
        · rintro (hqzero | hqlast)
          · exact Or.inr (Or.inr (Or.inr ⟨hqzero, trivial⟩))
          · exact Or.inr (Or.inl (by omega))
        · rintro (hforward | hback | hwrapFirst | hwrapLast)
          · omega
          · exact Or.inr (by omega)
          · omega
          · exact Or.inl hwrapLast.1
    · intro q
      refine Fin.lastCases ?_ (fun q => ?_) q
      · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        rw [G.adj_comm]
        rw [h.adj_iff p]
        unfold CyclicAdjacent
        simp only [Fin.val_last, Fin.val_castSucc]
        have := h.three_le
        constructor
        · rintro (hpzero | hplast)
          · exact Or.inr (Or.inr (Or.inl ⟨hpzero, trivial⟩))
          · exact Or.inl (by omega)
        · rintro (hforward | hback | hwrapFirst | hwrapLast)
          · exact Or.inr (by omega)
          · omega
          · exact Or.inl hwrapFirst.1
          · omega
      · simp only [Fin.lastCases_castSucc]
        rw [P.adj_iff p q]
        unfold CyclicAdjacent
        simp only [Fin.val_castSucc]
        omega

@[simp]
theorem closeToHole_card
    (P : IndexedInducedPath G) {s : V}
    (h : P.EndpointClosureData s) :
    (P.closeToHole h).card = P.card + 1 :=
  rfl

@[simp]
theorem closeToHole_vertex_last
    (P : IndexedInducedPath G) {s : V}
    (h : P.EndpointClosureData s) :
    (P.closeToHole h).vertex (Fin.last P.card) = s := by
  simp [closeToHole]

@[simp]
theorem closeToHole_vertex_castSucc
    (P : IndexedInducedPath G) {s : V}
    (h : P.EndpointClosureData s) (q : Fin P.card) :
    (P.closeToHole h).vertex (Fin.castSucc q) = P.vertex q := by
  simp [closeToHole]

/-- The closed hole has exactly the old path carrier plus its closing
vertex. -/
theorem range_closeToHole
    (P : IndexedInducedPath G) {s : V}
    (h : P.EndpointClosureData s) :
    Set.range (P.closeToHole h).vertex = Set.range P.vertex ∪ {s} := by
  ext v
  constructor
  · rintro ⟨q, hq⟩
    revert hq
    refine Fin.lastCases ?_ (fun q => ?_) q
    · intro hq
      right
      simpa [closeToHole] using hq.symm
    · intro hq
      left
      exact ⟨q, by simpa [closeToHole] using hq⟩
  · rintro (hv | rfl)
    · rcases hv with ⟨q, rfl⟩
      exact ⟨Fin.castSucc q, by simp [closeToHole]⟩
    · exact ⟨Fin.last P.card, by simp [closeToHole]⟩

end IndexedInducedPath

end SimpleGraph
