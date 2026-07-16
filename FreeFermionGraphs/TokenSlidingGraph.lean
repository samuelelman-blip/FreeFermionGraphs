import FreeFermionGraphs.TokenSlidingReachability

/-!
# The token-sliding solution graph

This file formalizes the solution graph `TSₖ(G)` from the paper.  Its vertices
are the `k`-vertex independent sets of `G`, and its edges are token slides.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- A vertex of the token-sliding solution graph: a `k`-vertex independent
set of `G`. -/
abbrev TokenConfiguration (G : SimpleGraph V) (k : Nat) :=
  {S : Finset V // G.IsNIndepSet k S}

/-- No set is related to itself by a token slide. -/
theorem TokenSlide.irrefl {G : SimpleGraph V} (S : Set V) :
    ¬G.TokenSlide S S := by
  intro h
  rcases h with h | h
  · rcases h with ⟨_, _, removed, _, _, hremoved, _, _⟩
    exact hremoved.2 hremoved.1
  · rcases h with ⟨_, _, removed, _, _, hremoved, _, _⟩
    exact hremoved.2 hremoved.1

/-- The solution graph `TSₖ(G)`: configurations are adjacent exactly when
they differ by one token slide. -/
def tokenSlideSolutionGraph (G : SimpleGraph V) (k : Nat) [DecidableEq V] :
    SimpleGraph (TokenConfiguration G k) where
  Adj S T := G.TokenSlide (S.1 : Set V) (T.1 : Set V)
  symm := ⟨by
    intro S T h
    exact TokenSlide.symm h⟩
  loopless := ⟨by
    intro S
    exact TokenSlide.irrefl (S.1 : Set V)⟩

@[simp]
theorem tokenSlideSolutionGraph_adj {G : SimpleGraph V} {k : Nat}
    [DecidableEq V] (S T : TokenConfiguration G k) :
    (G.tokenSlideSolutionGraph k).Adj S T ↔
      G.TokenSlide (S.1 : Set V) (T.1 : Set V) :=
  Iff.rfl

end SimpleGraph
