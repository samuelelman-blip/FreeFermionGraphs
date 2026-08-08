import FreeFermionGraphs.CliqueChargeFixedVertexOperatorAvoid

/-!
# Single-vertex charge recursion

This module proves the one-vertex form of the independent-set charge recursion
with an arbitrary previously deleted carrier.  It is the induction step used
to obtain manuscript Eq. (50) for a whole clique.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- Independent `(k+1)`-sets avoiding `W` split into those avoiding `j` and
those containing `j`. -/
theorem independentFinsetsOfCardAvoid_eq_union_singleVertex
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {W : Set V} {j : V} (k : Nat) :
    G.independentFinsetsOfCardAvoid W (k + 1) =
      G.independentFinsetsOfCardAvoid (W ∪ ({j} : Set V)) (k + 1) ∪
        G.independentFinsetsContainingAvoid W j k := by
  classical
  ext S
  constructor
  · intro hS
    rw [mem_independentFinsetsOfCardAvoid] at hS
    by_cases hjS : j ∈ S
    · rw [Finset.mem_union]
      exact Or.inr (mem_independentFinsetsContainingAvoid.mpr
        ⟨hS.1, hS.2.1, hS.2.2, hjS⟩)
    · rw [Finset.mem_union]
      apply Or.inl
      rw [mem_independentFinsetsOfCardAvoid]
      refine ⟨hS.1, hS.2.1, ?_⟩
      intro v hvS hvUnion
      rcases hvUnion with hvW | hvj
      · exact hS.2.2 v hvS hvW
      · have hvEq : v = j := by
          simpa using hvj
        apply hjS
        simpa [hvEq] using hvS
  · intro hS
    rw [Finset.mem_union] at hS
    rcases hS with hNo | hYes
    · rw [mem_independentFinsetsOfCardAvoid] at hNo ⊢
      refine ⟨hNo.1, hNo.2.1, ?_⟩
      intro v hvS hvW
      exact hNo.2.2 v hvS (Or.inl hvW)
    · rw [mem_independentFinsetsContainingAvoid] at hYes
      rw [mem_independentFinsetsOfCardAvoid]
      exact ⟨hYes.1, hYes.2.1, hYes.2.2.1⟩

/-- The two pieces in the single-vertex split are disjoint. -/
theorem independentFinsets_singleVertex_disjoint
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {W : Set V} {j : V} (k : Nat) :
    Disjoint
      (G.independentFinsetsOfCardAvoid (W ∪ ({j} : Set V)) (k + 1))
      (G.independentFinsetsContainingAvoid W j k) := by
  classical
  rw [Finset.disjoint_left]
  intro S hNo hYes
  rw [mem_independentFinsetsOfCardAvoid] at hNo
  rw [mem_independentFinsetsContainingAvoid] at hYes
  have hjNot : j ∉ S := by
    intro hjS
    exact hNo.2.2 j hjS (Or.inr (by simp))
  exact hjNot hYes.2.2.2

/-- Generalized one-vertex form of Eq. (50):

`Q_{G\W}^{(k+1)} = Q_{G\(W∪{j})}^{(k+1)}
  + h_j Q_{G\(W∪Γ[j])}^{(k)}`.
-/
theorem operatorIndependentSetCharge_singleVertex
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {W : Set V} {j : V} (hjW : j ∉ W) (k : Nat) :
    G.operatorIndependentSetCharge M W (k + 1) =
      G.operatorIndependentSetCharge M (W ∪ ({j} : Set V)) (k + 1) +
        M.term j * G.operatorIndependentSetCharge M
          (W ∪ G.closedNeighborhood j) k := by
  classical
  unfold operatorIndependentSetCharge
  rw [independentFinsetsOfCardAvoid_eq_union_singleVertex k]
  rw [Finset.sum_union (independentFinsets_singleVertex_disjoint k)]
  rw [sum_independentFinsetsContainingAvoid_eq_term_mul_charge M hjW k]
  rfl

end SimpleGraph
