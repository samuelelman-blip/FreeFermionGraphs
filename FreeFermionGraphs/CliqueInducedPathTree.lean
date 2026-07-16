import FreeFermionGraphs.InducedPathTree

/-!
# Induced-path trees rooted at a clique

Definition 17 adjoins a fresh vertex `j*` adjacent exactly to a clique `K`
and takes the induced-path tree rooted at `j*`.  We realize the augmented
vertex type as `Option V`, with `none` representing `j*`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- Adjacency after adjoining a fresh root to the vertices in `K`. -/
def AdjoinRootAdj (G : SimpleGraph V) (K : Set V) :
    Option V → Option V → Prop
  | some u, some v => G.Adj u v
  | none, some v => v ∈ K
  | some u, none => u ∈ K
  | none, none => False

theorem adjoinRootAdj_symm (G : SimpleGraph V) (K : Set V)
    {x y : Option V} (h : AdjoinRootAdj G K x y) :
    AdjoinRootAdj G K y x := by
  cases x with
  | none =>
      cases y with
      | none => exact h
      | some y => exact h
  | some x =>
      cases y with
      | none => exact h
      | some y => exact h.symm

theorem adjoinRootAdj_irrefl (G : SimpleGraph V) (K : Set V)
    (x : Option V) : ¬AdjoinRootAdj G K x x := by
  intro h
  cases x with
  | none => exact h
  | some x => exact G.irrefl h

/-- The augmented graph `G*` used in Definition 17. -/
def adjoinRootAt (G : SimpleGraph V) (K : Set V) : SimpleGraph (Option V) where
  Adj := AdjoinRootAdj G K
  symm := ⟨by
    intro x y h
    exact adjoinRootAdj_symm G K h⟩
  loopless := ⟨by
    intro x
    exact adjoinRootAdj_irrefl G K x⟩

@[simp]
theorem adjoinRootAt_adj_some_some (G : SimpleGraph V) (K : Set V)
    (u v : V) :
    (G.adjoinRootAt K).Adj (some u) (some v) ↔ G.Adj u v :=
  Iff.rfl

@[simp]
theorem adjoinRootAt_adj_none_some (G : SimpleGraph V) (K : Set V)
    (v : V) :
    (G.adjoinRootAt K).Adj none (some v) ↔ v ∈ K :=
  Iff.rfl

@[simp]
theorem adjoinRootAt_adj_some_none (G : SimpleGraph V) (K : Set V)
    (v : V) :
    (G.adjoinRootAt K).Adj (some v) none ↔ v ∈ K :=
  Iff.rfl

/-- Definition 17: the induced-path tree with respect to a clique `K`. -/
def inducedPathTreeAtClique (G : SimpleGraph V) (K : Set V)
    (_hK : G.IsClique K) :
    SimpleGraph
      (RootedInducedPath (G.adjoinRootAt K) (none : Option V)) :=
  (G.adjoinRootAt K).inducedPathTree none

end SimpleGraph
