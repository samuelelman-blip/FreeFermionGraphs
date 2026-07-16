import FreeFermionGraphs.InducedStructures

/-!
# Rooted induced-path trees

An equivalent, nonrecursive presentation of Definition 16.  A vertex of the
tree is an induced path beginning at the chosen root; tree edges join a path
to a one-vertex extension of that path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- An indexed induced path whose first vertex is `root`. -/
structure RootedInducedPath (G : SimpleGraph V) (root : V) where
  path : IndexedInducedPath G
  root_eq : path.vertex ⟨0, path.nonempty⟩ = root

namespace RootedInducedPath

variable {G : SimpleGraph V} {root : V}

/-- `Q` is obtained from `P` by appending exactly one vertex while preserving
the complete ordered prefix. -/
def IsOneVertexExtension (P Q : RootedInducedPath G root) : Prop :=
  ∃ hcard : P.path.card + 1 = Q.path.card,
    ∀ i : Fin P.path.card,
      Q.path.vertex ⟨i.val, by omega⟩ = P.path.vertex i

/-- A path cannot be its own one-vertex extension. -/
theorem not_isOneVertexExtension_self (P : RootedInducedPath G root) :
    ¬P.IsOneVertexExtension P := by
  rintro ⟨hcard, _⟩
  omega

/-- Adjacency in the rooted induced-path tree: either path is a one-vertex
extension of the other. -/
def TreeAdjacent (P Q : RootedInducedPath G root) : Prop :=
  P.IsOneVertexExtension Q ∨ Q.IsOneVertexExtension P

theorem treeAdjacent_comm (P Q : RootedInducedPath G root) :
    P.TreeAdjacent Q ↔ Q.TreeAdjacent P := by
  constructor <;> intro h
  · exact h.elim Or.inr Or.inl
  · exact h.elim Or.inr Or.inl

theorem not_treeAdjacent_self (P : RootedInducedPath G root) :
    ¬P.TreeAdjacent P := by
  intro h
  exact h.elim P.not_isOneVertexExtension_self
    P.not_isOneVertexExtension_self

end RootedInducedPath

/-- Definition 16: the induced-path tree rooted at `root`. -/
def inducedPathTree (G : SimpleGraph V) (root : V) :
    SimpleGraph (RootedInducedPath G root) where
  Adj := RootedInducedPath.TreeAdjacent
  symm := ⟨by
    intro P Q h
    exact (RootedInducedPath.treeAdjacent_comm P Q).mp h⟩
  loopless := ⟨by
    intro P
    exact RootedInducedPath.not_treeAdjacent_self P⟩

@[simp]
theorem inducedPathTree_adj {G : SimpleGraph V} {root : V}
    (P Q : RootedInducedPath G root) :
    (G.inducedPathTree root).Adj P Q ↔
      P.IsOneVertexExtension Q ∨ Q.IsOneVertexExtension P :=
  Iff.rfl

end SimpleGraph
