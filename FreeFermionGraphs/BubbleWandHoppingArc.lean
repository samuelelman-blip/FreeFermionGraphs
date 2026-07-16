import FreeFermionGraphs.DirectedHoppingGraph
import FreeFermionGraphs.EvenHoleLabeling

/-!
# Bubble-wand arcs in the directed hopping graph

This file instantiates the extra directed arcs in Definition 18.  A rooted
tree path is viewed through the original vertices it contains, excluding the
fresh clique root.  An extra arc points from the wand path to its handle when
the remaining hoop is an even hole.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

/-- The original `V`-vertices occurring in a path in the augmented graph;
the adjoined `none` root is discarded. -/
def originalCarrier {G : SimpleGraph V} {K : Set V}
    (P : RootedInducedPath (G.adjoinRootAt K) (none : Option V)) : Set V :=
  {v | ∃ i : Fin P.path.card, P.path.vertex i = some v}

end RootedInducedPath

/-- The concrete extra-arc relation from Definition 18.  The source is the
path of a bubble wand, the target is its handle, and the hoop is an even-hole
carrier. -/
def EvenHoopBubbleWandArc (G : SimpleGraph V) (K : Set V)
    (P P' : RootedInducedPath (G.adjoinRootAt K) (none : Option V)) : Prop :=
  ∃ B : BubbleWand G,
    P.originalCarrier = Set.range B.path.vertex ∧
    P'.originalCarrier = B.handle ∧
    ∃ (k : Nat) (C : EvenHoleLabeling G k), C.carrier = B.hoop

/-- Definition 18 specialized to the induced-path tree rooted at a clique. -/
def directedHoppingGraphAtClique (G : SimpleGraph V) (K : Set V)
    (hK : G.IsClique K) :
    ArcGraph
      (RootedInducedPath (G.adjoinRootAt K) (none : Option V)) :=
  directedHoppingGraph (G.inducedPathTreeAtClique K hK)
    (EvenHoopBubbleWandArc G K)

@[simp]
theorem directedHoppingGraphAtClique_arc_iff
    (G : SimpleGraph V) (K : Set V) (hK : G.IsClique K)
    (P P' : RootedInducedPath (G.adjoinRootAt K) (none : Option V)) :
    (G.directedHoppingGraphAtClique K hK).Arc P P' ↔
      (G.inducedPathTreeAtClique K hK).Adj P P' ∨
        EvenHoopBubbleWandArc G K P P' :=
  Iff.rfl

/-- A concrete even-hoop bubble wand produces its directed hopping arc. -/
theorem directedHoppingGraphAtClique_arc_of_bubbleWand
    {G : SimpleGraph V} {K : Set V} {hK : G.IsClique K}
    {P P' : RootedInducedPath (G.adjoinRootAt K) (none : Option V)}
    (B : BubbleWand G)
    (hsource : P.originalCarrier = Set.range B.path.vertex)
    (htarget : P'.originalCarrier = B.handle)
    {k : Nat} (C : EvenHoleLabeling G k) (hhoop : C.carrier = B.hoop) :
    (G.directedHoppingGraphAtClique K hK).Arc P P' := by
  apply directedHoppingGraph_arc_of_bubbleWand
  exact ⟨B, hsource, htarget, k, C, hhoop⟩

end SimpleGraph
