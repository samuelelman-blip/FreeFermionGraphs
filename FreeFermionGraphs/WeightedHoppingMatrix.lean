import Mathlib.Data.Matrix.Basic
import FreeFermionGraphs.BubbleWandHoppingArc

/-!
# The weighted directed-hopping matrix

This file formalises the piecewise weighted adjacency matrix in manuscript
Eq. (E1).  Its indices are the paths in the induced-path tree rooted at the
fresh clique vertex.  Extending a path has weight one, contracting its last
vertex `j` has weight `b_j ^ 2`, and an even-hoop bubble-wand arc has weight
`J_⟨C₀⟩ / N_{P,P',⟨C₀⟩}`.

The normalization and generalized-cycle eigenvalue are kept as explicit data.
Later Lemma 18 modules will construct the appropriate closure label for each
bubble-wand arc and prove the required normalization identity.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- The matrix-index type used by the clique-rooted directed hopping graph. -/
abbrev CliqueRootedInducedPath (G : SimpleGraph V) (K : Set V) :=
  RootedInducedPath (G.adjoinRootAt K) (none : Option V)

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- The final augmented-graph vertex of a clique-rooted induced path. -/
def terminalVertex (P : CliqueRootedInducedPath G K) : Option V :=
  P.path.vertex
    ⟨P.path.card - 1, Nat.sub_lt P.path.nonempty (by decide)⟩

/-- One-vertex extension is antisymmetric: two paths cannot each be a
one-vertex extension of the other. -/
theorem IsOneVertexExtension.not_reverse
    {root : Option V}
    {P Q : RootedInducedPath (G.adjoinRootAt K) root}
    (h : P.IsOneVertexExtension Q) :
    ¬Q.IsOneVertexExtension P := by
  rintro ⟨hQP, _⟩
  rcases h with ⟨hPQ, _⟩
  omega

end RootedInducedPath

/-- Algebraic data appearing in manuscript Eq. (E1).

`bubbleClosure P P'` names the deformation class `⟨C₀⟩` attached to a
bubble-wand arc.  The corresponding matrix entry is the generalized-cycle
eigenvalue divided by its normalization factor. -/
structure EqE1WeightData (G : SimpleGraph V) (K : Set V) (R : Type w) where
  coupling : V → R
  bubbleClosure :
    CliqueRootedInducedPath G K → CliqueRootedInducedPath G K → Set V
  generalizedCycleEigenvalue : Set V → R
  normalization :
    CliqueRootedInducedPath G K → CliqueRootedInducedPath G K → Set V → R

namespace EqE1WeightData

variable {G : SimpleGraph V} {K : Set V} {R : Type w}

/-- The `b_j ^ 2` contraction entry in Eq. (E1).  The `none` branch can only
refer to the fresh root and is zero; genuine contractions remove an original
vertex, as proved at the path-prefix layer. -/
def contractionWeight [Field R] (W : EqE1WeightData G K R)
    (P : CliqueRootedInducedPath G K) : R :=
  match P.terminalVertex with
  | none => 0
  | some j => W.coupling j ^ 2

/-- The normalized generalized-cycle entry in Eq. (E1). -/
def bubbleWeight [Field R] (W : EqE1WeightData G K R)
    (P P' : CliqueRootedInducedPath G K) : R :=
  W.generalizedCycleEigenvalue (W.bubbleClosure P P') /
    W.normalization P P' (W.bubbleClosure P P')

end EqE1WeightData

/-- Manuscript Eq. (E1), represented literally as a matrix on clique-rooted
induced paths.  The order of the cases is the order printed in the paper. -/
noncomputable def eqE1WeightedAdjacency
    {R : Type w} [Field R]
    (G : SimpleGraph V) (K : Set V) (W : EqE1WeightData G K R) :
    Matrix (CliqueRootedInducedPath G K) (CliqueRootedInducedPath G K) R := by
  classical
  exact fun P P' =>
    if P.IsOneVertexExtension P' then
      1
    else if P'.IsOneVertexExtension P then
      W.contractionWeight P
    else if EvenHoopBubbleWandArc G K P P' then
      W.bubbleWeight P P'
    else
      0

@[simp]
theorem eqE1WeightedAdjacency_of_extension
    {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]
    (W : EqE1WeightData G K R)
    {P P' : CliqueRootedInducedPath G K}
    (h : P.IsOneVertexExtension P') :
    eqE1WeightedAdjacency G K W P P' = 1 := by
  classical
  simp [eqE1WeightedAdjacency, h]

@[simp]
theorem eqE1WeightedAdjacency_of_contraction
    {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]
    (W : EqE1WeightData G K R)
    {P P' : CliqueRootedInducedPath G K}
    (h : P'.IsOneVertexExtension P) :
    eqE1WeightedAdjacency G K W P P' = W.contractionWeight P := by
  classical
  simp [eqE1WeightedAdjacency, h, h.not_reverse]

/-- The contraction case is exactly `b_j ^ 2` when the removed terminal
vertex is `j`. -/
theorem eqE1WeightedAdjacency_of_contraction_at
    {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]
    (W : EqE1WeightData G K R)
    {P P' : CliqueRootedInducedPath G K} {j : V}
    (h : P'.IsOneVertexExtension P)
    (hterminal : P.terminalVertex = some j) :
    eqE1WeightedAdjacency G K W P P' = W.coupling j ^ 2 := by
  rw [eqE1WeightedAdjacency_of_contraction W h]
  simp [EqE1WeightData.contractionWeight, hterminal]

@[simp]
theorem eqE1WeightedAdjacency_of_bubbleWand
    {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]
    (hK : G.IsClique K) (W : EqE1WeightData G K R)
    {P P' : CliqueRootedInducedPath G K}
    (htree : ¬(G.inducedPathTreeAtClique K hK).Adj P P')
    (hbubble : EvenHoopBubbleWandArc G K P P') :
    eqE1WeightedAdjacency G K W P P' = W.bubbleWeight P P' := by
  classical
  have hforward : ¬P.IsOneVertexExtension P' := by
    intro h
    exact htree (Or.inl h)
  have hbackward : ¬P'.IsOneVertexExtension P := by
    intro h
    exact htree (Or.inr h)
  simp [eqE1WeightedAdjacency, hforward, hbackward, hbubble]

/-- Eq. (E1) vanishes away from the arcs of the directed hopping graph. -/
theorem eqE1WeightedAdjacency_eq_zero_of_not_arc
    {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]
    (hK : G.IsClique K) (W : EqE1WeightData G K R)
    {P P' : CliqueRootedInducedPath G K}
    (h : ¬(G.directedHoppingGraphAtClique K hK).Arc P P') :
    eqE1WeightedAdjacency G K W P P' = 0 := by
  classical
  have htree : ¬(G.inducedPathTreeAtClique K hK).Adj P P' := by
    intro hadj
    exact h (Or.inl hadj)
  have hforward : ¬P.IsOneVertexExtension P' := by
    intro hforward
    exact htree (Or.inl hforward)
  have hbackward : ¬P'.IsOneVertexExtension P := by
    intro hbackward
    exact htree (Or.inr hbackward)
  have hbubble : ¬EvenHoopBubbleWandArc G K P P' := by
    intro hbubble
    exact h (Or.inr hbubble)
  simp [eqE1WeightedAdjacency, hforward, hbackward, hbubble]

/-- Every nonzero Eq. (E1) entry is supported on an arc of Definition 18. -/
theorem eqE1WeightedAdjacency_ne_zero_imp_arc
    {G : SimpleGraph V} {K : Set V} {R : Type w} [Field R]
    (hK : G.IsClique K) (W : EqE1WeightData G K R)
    {P P' : CliqueRootedInducedPath G K}
    (h : eqE1WeightedAdjacency G K W P P' ≠ 0) :
    (G.directedHoppingGraphAtClique K hK).Arc P P' := by
  by_contra harc
  exact h (eqE1WeightedAdjacency_eq_zero_of_not_arc hK W harc)

end SimpleGraph
