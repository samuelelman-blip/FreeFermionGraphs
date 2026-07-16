import FreeFermionGraphs.BubbleWand

/-!
# Directed hopping graphs

Definition 18 has two kinds of arcs: both orientations of every edge in an
induced-path tree, and additional directed arcs supplied by even-hoop bubble
wands.  This file isolates that directed-graph construction; the concrete
bubble-wand arc predicate can then be instantiated independently.
-/

universe u

namespace SimpleGraph

/-- A directed graph represented by its arc relation.  Loops are not excluded
at this level because direction-specific constructions may impose their own
conditions. -/
structure ArcGraph (α : Type u) where
  Arc : α → α → Prop

namespace ArcGraph

variable {α : Type u}

/-- Replace every edge of a simple graph by the two corresponding directed
arcs. -/
def bidirected (T : SimpleGraph α) : ArcGraph α where
  Arc := T.Adj

@[simp]
theorem bidirected_arc (T : SimpleGraph α) (x y : α) :
    (bidirected T).Arc x y ↔ T.Adj x y :=
  Iff.rfl

/-- Add a directed relation of extra arcs to an existing directed graph. -/
def addArcs (D : ArcGraph α) (extra : α → α → Prop) : ArcGraph α where
  Arc x y := D.Arc x y ∨ extra x y

@[simp]
theorem addArcs_arc (D : ArcGraph α) (extra : α → α → Prop)
    (x y : α) :
    (D.addArcs extra).Arc x y ↔ D.Arc x y ∨ extra x y :=
  Iff.rfl

end ArcGraph

/-- Definition 18: bidirect every edge of the induced-path tree and add the
directed arcs arising from even-hoop bubble wands. -/
def directedHoppingGraph {α : Type u} (tree : SimpleGraph α)
    (bubbleWandArc : α → α → Prop) : ArcGraph α :=
  (ArcGraph.bidirected tree).addArcs bubbleWandArc

@[simp]
theorem directedHoppingGraph_arc_iff {α : Type u}
    (tree : SimpleGraph α) (bubbleWandArc : α → α → Prop)
    (P P' : α) :
    (directedHoppingGraph tree bubbleWandArc).Arc P P' ↔
      tree.Adj P P' ∨ bubbleWandArc P P' :=
  Iff.rfl

/-- Every tree edge supplies its forward hopping arc. -/
theorem directedHoppingGraph_arc_of_adj {α : Type u}
    {tree : SimpleGraph α} {bubbleWandArc : α → α → Prop}
    {P P' : α} (h : tree.Adj P P') :
    (directedHoppingGraph tree bubbleWandArc).Arc P P' :=
  Or.inl h

/-- Every tree edge also supplies its reverse hopping arc. -/
theorem directedHoppingGraph_reverse_arc_of_adj {α : Type u}
    {tree : SimpleGraph α} {bubbleWandArc : α → α → Prop}
    {P P' : α} (h : tree.Adj P P') :
    (directedHoppingGraph tree bubbleWandArc).Arc P' P :=
  Or.inl h.symm

/-- Every certified bubble-wand transition supplies its additional directed
hopping arc. -/
theorem directedHoppingGraph_arc_of_bubbleWand {α : Type u}
    {tree : SimpleGraph α} {bubbleWandArc : α → α → Prop}
    {P P' : α} (h : bubbleWandArc P P') :
    (directedHoppingGraph tree bubbleWandArc).Arc P P' :=
  Or.inr h

end SimpleGraph
