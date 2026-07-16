import FreeFermionGraphs.TokenSlidingGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Components of the token-sliding solution graph

The connected components of `TSₖ(G)` are the paper's set `Ξₖ`.  This file
records the precise equivalence between belonging to the same component and
token-slide reachability in the solution graph.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- The paper's `Ξₖ`: connected components of the token-sliding solution
graph. -/
abbrev TokenSlidingComponent (G : SimpleGraph V) (k : Nat) [DecidableEq V] :=
  (G.tokenSlideSolutionGraph k).ConnectedComponent

/-- The token-sliding component containing a configuration. -/
def tokenSlidingComponentMk (G : SimpleGraph V) (k : Nat) [DecidableEq V]
    (S : TokenConfiguration G k) : TokenSlidingComponent G k :=
  (G.tokenSlideSolutionGraph k).connectedComponentMk S

/-- Two configurations represent the same element of `Ξₖ` exactly when they
are reachable in `TSₖ(G)`. -/
@[simp]
theorem tokenSlidingComponentMk_eq_iff {G : SimpleGraph V} {k : Nat}
    [DecidableEq V] (S T : TokenConfiguration G k) :
    G.tokenSlidingComponentMk k S = G.tokenSlidingComponentMk k T ↔
      (G.tokenSlideSolutionGraph k).Reachable S T := by
  exact ConnectedComponent.eq

/-- A single token slide keeps configurations in the same component. -/
theorem TokenSlide.same_tokenSlidingComponent {G : SimpleGraph V} {k : Nat}
    [DecidableEq V] {S T : TokenConfiguration G k}
    (h : G.TokenSlide (S.1 : Set V) (T.1 : Set V)) :
    G.tokenSlidingComponentMk k S = G.tokenSlidingComponentMk k T := by
  exact ConnectedComponent.connectedComponentMk_eq_of_adj h

end SimpleGraph
