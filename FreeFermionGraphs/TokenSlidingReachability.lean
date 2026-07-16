import FreeFermionGraphs.TokenSliding

/-!
# Token-slide reachability

Basic relation-theoretic properties of the paper's `↔TS` relation.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

/-- Reverse a token slide. -/
theorem TokenSlide.symm {G : SimpleGraph V} {S T : Set V}
    (h : G.TokenSlide S T) : G.TokenSlide T S :=
  tokenSlide_comm.mp h

/-- Concatenate two finite token-slide sequences. -/
theorem TokenSlideReachable.trans {G : SimpleGraph V} {S T U : Set V}
    (hST : G.TokenSlideReachable S T)
    (hTU : G.TokenSlideReachable T U) :
    G.TokenSlideReachable S U := by
  induction hTU with
  | refl => exact hST
  | tail hTU hstep ih =>
      exact TokenSlideReachable.tail ih hstep

/-- Reverse a finite token-slide sequence. -/
theorem TokenSlideReachable.symm {G : SimpleGraph V} {S T : Set V}
    (hST : G.TokenSlideReachable S T) :
    G.TokenSlideReachable T S := by
  induction hST with
  | refl => exact TokenSlideReachable.refl _
  | tail hST hstep ih =>
      exact TokenSlideReachable.trans
        (TokenSlide.reachable (TokenSlide.symm hstep)) ih

/-- Token-slide reachability is symmetric, as asserted after equation (A4). -/
theorem tokenSlideReachable_comm {G : SimpleGraph V} {S T : Set V} :
    G.TokenSlideReachable S T ↔ G.TokenSlideReachable T S := by
  constructor
  · exact TokenSlideReachable.symm
  · exact TokenSlideReachable.symm

end SimpleGraph
