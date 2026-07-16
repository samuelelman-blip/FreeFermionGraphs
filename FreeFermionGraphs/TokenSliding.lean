import FreeFermionGraphs.Corollary6
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Token-sliding reconfiguration

Graph-theoretic foundations for Definition 13 of the paper.  A forward move
replaces one vertex of an independent set by an adjacent vertex; `TokenSlide`
forgets the orientation, and `TokenSlideReachable` records a finite sequence
of such moves.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- An oriented token slide from `S` to `T`: remove `removed`, slide its token
across an edge to `added`, and require both endpoint sets to be independent. -/
def ForwardTokenSlide (G : SimpleGraph V) (S T : Set V) : Prop :=
  G.IsIndepSet S ∧ G.IsIndepSet T ∧
    ∃ removed added : V,
      G.Adj removed added ∧
      removed ∈ S \ T ∧
      added ∈ T \ S ∧
      T = Set.insert added (S \ {removed})

/-- Definition 13: two independent sets are related by a token slide.  The
disjunction makes the reversibility stated after (A4) definitional. -/
def TokenSlide (G : SimpleGraph V) (S T : Set V) : Prop :=
  ForwardTokenSlide G S T ∨ ForwardTokenSlide G T S

/-- The token-slide relation is symmetric. -/
theorem tokenSlide_comm {G : SimpleGraph V} {S T : Set V} :
    G.TokenSlide S T ↔ G.TokenSlide T S := by
  constructor <;> intro h
  · exact h.elim Or.inr Or.inl
  · exact h.elim Or.inr Or.inl

/-- Reachability by a finite sequence of token slides, written
`S ↔TS T` in the paper. -/
inductive TokenSlideReachable (G : SimpleGraph V) : Set V → Set V → Prop
  | refl (S : Set V) : TokenSlideReachable G S S
  | tail {S T U : Set V} :
      TokenSlideReachable G S T →
      TokenSlide G T U →
      TokenSlideReachable G S U

/-- One token slide gives a one-step reachability proof. -/
theorem TokenSlide.reachable {G : SimpleGraph V} {S T : Set V}
    (h : G.TokenSlide S T) : G.TokenSlideReachable S T :=
  TokenSlideReachable.tail (TokenSlideReachable.refl S) h

end SimpleGraph
