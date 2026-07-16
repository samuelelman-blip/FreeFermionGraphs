import FreeFermionGraphs.Corollary9
import FreeFermionGraphs.Deformation

/-!
# Anticommuting and dependent subsets

The combinatorial part of Definition 20.  The operator-dependent condition
defining `W` is kept as a predicate, while `U` is represented directly by
adjacency to the introduced vertex and nonmembership in the closed
neighborhood of the removed vertex.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Definition 20's set `W`: vertices in `C' \ C` whose terms
anticommute with the cycle term. -/
def anticommutingSubset (C C' : Set V)
    (Anticommutes : V → Prop) : Set V :=
  {w | w ∈ C' ∧ w ∉ C ∧ Anticommutes w}

@[simp]
theorem mem_anticommutingSubset {C C' : Set V}
    {Anticommutes : V → Prop} {w : V} :
    w ∈ anticommutingSubset C C' Anticommutes ↔
      w ∈ C' ∧ w ∉ C ∧ Anticommutes w :=
  Iff.rfl

/-- Definition 20's dependent subset
`Γ_{C'}(introduced) \ Γ_{C'}[removed]`. -/
def dependentSubset (G : SimpleGraph V) (C' : Set V)
    (introduced removed : V) : Set V :=
  {u | u ∈ C' ∧ G.Adj u introduced ∧
    u ≠ removed ∧ ¬G.Adj u removed}

@[simp]
theorem mem_dependentSubset {C' : Set V}
    {introduced removed u : V} :
    u ∈ G.dependentSubset C' introduced removed ↔
      u ∈ C' ∧ G.Adj u introduced ∧
        u ≠ removed ∧ ¬G.Adj u removed :=
  Iff.rfl

/-- The union `U` of all dependent subsets in a deformation. -/
def dependentUnion {ι : Type*} (U : ι → Set V) : Set V :=
  ⋃ x, U x

@[simp]
theorem mem_dependentUnion_iff {ι : Type*} {U : ι → Set V} {u : V} :
    u ∈ dependentUnion U ↔ ∃ x, u ∈ U x := by
  simp [dependentUnion]

/-- A dependent vertex cannot be the removed vertex. -/
theorem removed_not_mem_dependentSubset (C' : Set V)
    (introduced removed : V) :
    removed ∉ G.dependentSubset C' introduced removed := by
  intro h
  exact h.2.2.1 rfl

/-- The common-neighbor statement used in Corollary 10.  For a deformation
that replaces `C.vertex i` by `introduced`, an external dependent vertex
has a hole vertex adjacent to it, the introduced vertex, and the removed
vertex. -/
theorem dependentSubset_has_common_hole_neighbor
    {C : IndexedInducedHole G} {C' : Set V}
    {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (hclaw : G.IsClawFree)
    (hu : u ∈ G.dependentSubset C' introduced (C.vertex i))
    (huOutside : u ∉ Set.insert introduced (Set.range C.vertex)) :
    ∃ v ∈ Set.range C.vertex,
      G.Adj u v ∧
      G.Adj introduced v ∧
      G.Adj (C.vertex i) v := by
  rcases h.dependent_hits_cycle_neighbor hclaw huOutside
      (Or.inl ⟨hu.2.1, hu.2.2.2⟩) with ⟨q, hiq, huq⟩
  exact ⟨C.vertex q, ⟨q, rfl⟩, huq,
    h.adj_of_clone_adj hiq, hiq⟩

end SimpleGraph
