import FreeFermionGraphs.Neighboring
import Lean.Elab.Tactic.Omega

/-!
# Indexed induced paths and holes

Concrete order-sensitive representations of the paths and holes used in the
neighboring-relation classification.  These structures keep the vertex order
available while recording that the ambient graph has exactly the prescribed
edges on the indexed vertices.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Two indices are consecutive in the cyclic order on `Fin n`. -/
def CyclicAdjacent {n : Nat} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n)

theorem CyclicAdjacent.symm {n : Nat} {i j : Fin n}
    (h : CyclicAdjacent i j) : CyclicAdjacent j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- An induced path equipped with its linear vertex order. -/
structure IndexedInducedPath (G : SimpleGraph V) where
  card : Nat
  nonempty : 0 < card
  vertex : Fin card → V
  injective : Function.Injective vertex
  adj_iff : ∀ i j,
    G.Adj (vertex i) (vertex j) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- An induced hole equipped with its cyclic vertex order.  Holes have at
least four vertices. -/
structure IndexedInducedHole (G : SimpleGraph V) where
  card : Nat
  four_le_card : 4 ≤ card
  vertex : Fin card → V
  injective : Function.Injective vertex
  adj_iff : ∀ i j,
    G.Adj (vertex i) (vertex j) ↔ CyclicAdjacent i j

/-- Three consecutive vertices of an indexed induced path form an induced
three-vertex path in the ambient graph. -/
theorem IndexedInducedPath.consecutiveTriple
    (P : IndexedInducedPath G) {i₀ i₁ i₂ : Fin P.card}
    (h₀₁ : i₀.val + 1 = i₁.val) (h₁₂ : i₁.val + 1 = i₂.val) :
    G.IsInducedPathTriple (P.vertex i₀) (P.vertex i₁) (P.vertex i₂) := by
  refine ⟨(P.adj_iff i₀ i₁).2 (Or.inl h₀₁),
    (P.adj_iff i₁ i₂).2 (Or.inl h₁₂), ?_, ?_⟩
  · intro h
    rcases (P.adj_iff i₀ i₂).1 h with h | h <;> omega
  · intro h
    have hi := P.injective h
    have hval := congrArg Fin.val hi
    omega

/-- Every vertex of an indexed hole has two distinct, nonadjacent cycle
neighbors. -/
theorem IndexedInducedHole.exists_two_nonadjacent_neighbors
    (C : IndexedInducedHole G) (i : Fin C.card) :
    ∃ u v : Fin C.card, u ≠ v ∧
      G.Adj (C.vertex i) (C.vertex u) ∧
      G.Adj (C.vertex i) (C.vertex v) ∧
      ¬G.Adj (C.vertex u) (C.vertex v) := by
  have hcard : 4 ≤ C.card := C.four_le_card
  have hi : i.val < C.card := i.isLt
  by_cases hfirst : i.val = 0
  · let u : Fin C.card := ⟨1, by omega⟩
    let v : Fin C.card := ⟨C.card - 1, by omega⟩
    refine ⟨u, v, ?_, (C.adj_iff i u).2 ?_, (C.adj_iff i v).2 ?_, ?_⟩
    · intro h
      have hval := congrArg Fin.val h
      dsimp [u, v] at hval
      omega
    · unfold CyclicAdjacent
      left
      dsimp [u]
      omega
    · unfold CyclicAdjacent
      exact Or.inr (Or.inr (Or.inl ⟨hfirst, by dsimp [v]; omega⟩))
    · intro h
      have hadj := (C.adj_iff u v).1 h
      unfold CyclicAdjacent at hadj
      dsimp [u, v] at hadj
      omega
  · by_cases hlast : i.val + 1 = C.card
    · let u : Fin C.card := ⟨0, by omega⟩
      let v : Fin C.card := ⟨C.card - 2, by omega⟩
      refine ⟨u, v, ?_, (C.adj_iff i u).2 ?_, (C.adj_iff i v).2 ?_, ?_⟩
      · intro h
        have hval := congrArg Fin.val h
        dsimp [u, v] at hval
        omega
      · unfold CyclicAdjacent
        exact Or.inr (Or.inr (Or.inr ⟨by rfl, hlast⟩))
      · unfold CyclicAdjacent
        right
        left
        dsimp [v]
        omega
      · intro h
        have hadj := (C.adj_iff u v).1 h
        unfold CyclicAdjacent at hadj
        dsimp [u, v] at hadj
        omega
    · let u : Fin C.card := ⟨i.val - 1, by omega⟩
      let v : Fin C.card := ⟨i.val + 1, by omega⟩
      refine ⟨u, v, ?_, (C.adj_iff i u).2 ?_, (C.adj_iff i v).2 ?_, ?_⟩
      · intro h
        have hval := congrArg Fin.val h
        dsimp [u, v] at hval
        omega
      · unfold CyclicAdjacent
        right
        left
        dsimp [u]
        omega
      · unfold CyclicAdjacent
        left
        dsimp [v]
      · intro h
        have hadj := (C.adj_iff u v).1 h
        unfold CyclicAdjacent at hadj
        dsimp [u, v] at hadj
        omega

/-- Indexed form of Corollary 2: an external neighbor of a hole vertex also
neighbors at least one of its two cycle neighbors. -/
theorem IndexedInducedHole.external_neighbor_hits_cycle_neighbor
    (C : IndexedInducedHole G) (hclaw : G.IsClawFree) {j : V}
    (hjC : j ∉ Set.range C.vertex) (i : Fin C.card)
    (hji : G.Adj j (C.vertex i)) :
    ∃ u v : Fin C.card, u ≠ v ∧
      G.Adj (C.vertex i) (C.vertex u) ∧
      G.Adj (C.vertex i) (C.vertex v) ∧
      ¬G.Adj (C.vertex u) (C.vertex v) ∧
      (G.Adj j (C.vertex u) ∨ G.Adj j (C.vertex v)) := by
  obtain ⟨u, v, huv, hiu, hiv, huv_nonadj⟩ :=
    C.exists_two_nonadjacent_neighbors i
  have hju : j ≠ C.vertex u := by
    intro h
    exact hjC ⟨u, h.symm⟩
  have hjv : j ≠ C.vertex v := by
    intro h
    exact hjC ⟨v, h.symm⟩
  have huv_vertices : C.vertex u ≠ C.vertex v := by
    intro h
    exact huv (C.injective h)
  refine ⟨u, v, huv, hiu, hiv, huv_nonadj, ?_⟩
  exact hclaw.adjacent_to_one_of_nonadjacent_neighbors
    hji hiu hiv hju hjv huv_vertices huv_nonadj

end SimpleGraph
