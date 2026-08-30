import FreeFermionGraphs.PauliCliqueHamiltonianEndpointExtension
import FreeFermionGraphs.BubbleWandHoppingArc
import FreeFermionGraphs.InducedPathDeformationBubbleWand

/-!
# Removing the artificial root from a clique-rooted path

Every positive-index vertex of a clique-rooted path is an original graph
vertex.  This module packages those vertices, in their inherited order, as
an indexed induced path in the original graph.  The resulting carrier is
exactly the `originalCarrier` used by the bubble-wand arcs in Definition 18.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- The positive augmented-path index corresponding to an index of the
original tail. -/
def originalTailIndex
    (P : CliqueRootedInducedPath G K) (hcard : 2 ≤ P.path.card)
    (i : Fin (P.path.card - 1)) : Fin P.path.card :=
  ⟨i.val + 1, by omega⟩

/-- The original vertex at a positive augmented-path index. -/
noncomputable def originalTailVertex
    (P : CliqueRootedInducedPath G K) (hcard : 2 ≤ P.path.card)
    (i : Fin (P.path.card - 1)) : V :=
  Classical.choose (P.vertex_eq_some_of_pos (P.originalTailIndex hcard i)
    (by simp [originalTailIndex]))

@[simp]
theorem path_vertex_originalTailIndex
    (P : CliqueRootedInducedPath G K) (hcard : 2 ≤ P.path.card)
    (i : Fin (P.path.card - 1)) :
    P.path.vertex (P.originalTailIndex hcard i) =
      some (P.originalTailVertex hcard i) := by
  exact Classical.choose_spec
    (P.vertex_eq_some_of_pos (P.originalTailIndex hcard i)
      (by simp [originalTailIndex]))

/-- The clique-rooted path with its artificial root removed, viewed as an
indexed induced path in the original graph. -/
noncomputable def originalTail
    (P : CliqueRootedInducedPath G K) (hcard : 2 ≤ P.path.card) :
    IndexedInducedPath G where
  card := P.path.card - 1
  nonempty := by omega
  vertex := P.originalTailVertex hcard
  injective := by
    intro i j hij
    apply Fin.ext
    have hsome := congrArg some hij
    have hindices := P.path.injective
      ((P.path_vertex_originalTailIndex hcard i).trans
        (hsome.trans (P.path_vertex_originalTailIndex hcard j).symm))
    exact Nat.add_right_cancel
      (show i.val + 1 = j.val + 1 from congrArg Fin.val hindices)
  adj_iff := by
    intro i j
    rw [← G.adjoinRootAt_adj_some_some K]
    rw [← P.path_vertex_originalTailIndex hcard i,
      ← P.path_vertex_originalTailIndex hcard j]
    rw [P.path.adj_iff]
    simp only [originalTailIndex]
    constructor <;> rintro (h | h)
    · left
      omega
    · right
      omega
    · left
      omega
    · right
      omega

@[simp]
theorem originalTail_card
    (P : CliqueRootedInducedPath G K) (hcard : 2 ≤ P.path.card) :
    (P.originalTail hcard).card = P.path.card - 1 :=
  rfl

@[simp]
theorem originalTail_vertex
    (P : CliqueRootedInducedPath G K) (hcard : 2 ≤ P.path.card)
    (i : Fin (P.path.card - 1)) :
    (P.originalTail hcard).vertex i = P.originalTailVertex hcard i :=
  rfl

/-- Removing the artificial root does not change the original-vertex
carrier. -/
theorem originalCarrier_eq_range_originalTail
    (P : CliqueRootedInducedPath G K) (hcard : 2 ≤ P.path.card) :
    P.originalCarrier = Set.range (P.originalTail hcard).vertex := by
  ext v
  constructor
  · rintro ⟨q, hq⟩
    have hqpos : 0 < q.val := by
      by_contra hnot
      have hqzero : q = ⟨0, P.path.nonempty⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_not_pos hnot
      rw [hqzero, P.root_eq] at hq
      simp at hq
    let i : Fin (P.path.card - 1) := ⟨q.val - 1, by omega⟩
    refine ⟨i, ?_⟩
    apply Option.some.inj
    have hindex : P.originalTailIndex hcard i = q := by
      apply Fin.ext
      dsimp [i, originalTailIndex]
      omega
    exact (P.path_vertex_originalTailIndex hcard i).symm.trans
      (hindex ▸ hq)
  · rintro ⟨i, hi⟩
    refine ⟨P.originalTailIndex hcard i, ?_⟩
    rw [P.path_vertex_originalTailIndex hcard i]
    exact congrArg some hi

end RootedInducedPath

end SimpleGraph
