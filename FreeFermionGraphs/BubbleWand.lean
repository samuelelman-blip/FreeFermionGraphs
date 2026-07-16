import FreeFermionGraphs.CliqueInducedPathTree

/-!
# Bubble wands

Definition 11 of the paper.  A bubble vertex outside an induced path is
adjacent exactly to two consecutive path vertices and the final endpoint.
The initial path segment is the handle; removing it from the full carrier
leaves the hoop.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- A bubble wand with neighboring pattern
`Γ_P(j) = {j_i, j_{i+1}, j_ℓ}` and `i < ℓ - 2`. -/
structure BubbleWand (G : SimpleGraph V) where
  path : IndexedInducedPath G
  bubble : V
  split : Fin path.card
  gap : split.val + 3 < path.card
  outside : bubble ∉ Set.range path.vertex
  adj_iff : ∀ q : Fin path.card,
    G.Adj bubble (path.vertex q) ↔
      q.val = split.val ∨
      q.val = split.val + 1 ∨
      q.val + 1 = path.card

namespace BubbleWand

variable {G : SimpleGraph V}

/-- The vertex immediately after the handle. -/
def nextIndex (B : BubbleWand G) : Fin B.path.card :=
  ⟨B.split.val + 1, by
    have hgap := B.gap
    omega⟩

/-- The final endpoint index of the underlying path. -/
def lastIndex (B : BubbleWand G) : Fin B.path.card :=
  ⟨B.path.card - 1, by
    have hpos : 0 < B.path.card := B.path.nonempty
    omega⟩

/-- The carrier of the full bubble-wand graph `B = P ∪ {j}`. -/
def carrier (B : BubbleWand G) : Set V :=
  Set.range B.path.vertex ∪ {B.bubble}

/-- The handle `P_i`, including path vertices from index zero through the
split index. -/
def handle (B : BubbleWand G) : Set V :=
  {v | ∃ q : Fin B.path.card,
    q.val ≤ B.split.val ∧ B.path.vertex q = v}

/-- The hoop `C = B \ P_i`. -/
def hoop (B : BubbleWand G) : Set V :=
  B.carrier \ B.handle

@[simp]
theorem bubble_mem_carrier (B : BubbleWand G) :
    B.bubble ∈ B.carrier := by
  exact Or.inr rfl

theorem bubble_not_mem_handle (B : BubbleWand G) :
    B.bubble ∉ B.handle := by
  rintro ⟨q, _, hq⟩
  exact B.outside ⟨q, hq⟩

@[simp]
theorem bubble_mem_hoop (B : BubbleWand G) :
    B.bubble ∈ B.hoop :=
  ⟨B.bubble_mem_carrier, B.bubble_not_mem_handle⟩

/-- The bubble is adjacent to the final handle vertex. -/
theorem adj_split (B : BubbleWand G) :
    G.Adj B.bubble (B.path.vertex B.split) := by
  exact (B.adj_iff B.split).2 (Or.inl rfl)

/-- The bubble is adjacent to the first path vertex in the hoop. -/
theorem adj_next (B : BubbleWand G) :
    G.Adj B.bubble (B.path.vertex B.nextIndex) := by
  apply (B.adj_iff B.nextIndex).2
  exact Or.inr (Or.inl rfl)

/-- The bubble is adjacent to the terminal endpoint of the path. -/
theorem adj_last (B : BubbleWand G) :
    G.Adj B.bubble (B.path.vertex B.lastIndex) := by
  apply (B.adj_iff B.lastIndex).2
  exact Or.inr (Or.inr (by
    change B.path.card - 1 + 1 = B.path.card
    have hpos : 0 < B.path.card := B.path.nonempty
    omega))

end BubbleWand

end SimpleGraph
