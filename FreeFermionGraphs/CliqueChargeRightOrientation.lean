import FreeFermionGraphs.CliqueChargeCliqueRecursion

/-!
# Right-oriented clique charge recursion

The manuscript states Eq. (50) with `h_j` on the left, but in the proof of
Lemma 17 the corresponding terms are written with the deleted charge on the
left of `h_j`.  This module records the commutation step explicitly.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- If an independent configuration avoids the closed neighborhood of `j`,
then its operator product commutes with `h_j`.

Both multiplication orders are identified with the same inserted independent
product. -/
theorem independentProduct_commutes_term_of_avoids_closedNeighborhood
    {G : SimpleGraph V} [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {j : V} {S : Finset V}
    (hSind : G.IsIndepSet (S : Set V))
    (hSavoid : ∀ v ∈ S, v ∉ G.closedNeighborhood j) :
    M.independentProduct S * M.term j =
      M.term j * M.independentProduct S := by
  have hjNotS : j ∉ S := by
    intro hjS
    exact hSavoid j hjS (by simp [closedNeighborhood])
  have hnonadj : ∀ v ∈ S, ¬G.Adj j v := by
    intro v hvS hadj
    apply hSavoid v hvS
    exact Set.mem_insert_iff.mpr
      (Or.inr ((G.mem_neighborSet j v).mpr hadj))
  have hleft :=
    M.independentProduct_insert_left hjNotS hSind hnonadj
  have hright :=
    M.independentProduct_insert_right hjNotS hSind hnonadj
  exact hright.symm.trans hleft

/-- A charge on a graph with `Γ[j]` deleted commutes with `h_j`.  An
additional deleted carrier `W` is allowed because it only removes further
summands. -/
theorem operatorIndependentSetCharge_commutes_term_closedNeighborhood
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    (W : Set V) (j : V) (k : Nat) :
    G.operatorIndependentSetCharge M
        (W ∪ G.closedNeighborhood j) k * M.term j =
      M.term j *
        G.operatorIndependentSetCharge M
          (W ∪ G.closedNeighborhood j) k := by
  classical
  unfold operatorIndependentSetCharge
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [mem_independentFinsetsOfCardAvoid] at hS
  apply independentProduct_commutes_term_of_avoids_closedNeighborhood
    M hS.2.1
  intro v hvS hvClosed
  exact hS.2.2 v hvS (Or.inr hvClosed)

/-- Finite-clique form of Eq. (50) with the manuscript Lemma 17 multiplication
orientation:

`Q_{G\W}^{(k+1)} = Q_{G\(W∪K)}^{(k+1)}
  + ∑_{j∈K} Q_{G\(W∪Γ[j])}^k h_j`.
-/
theorem operatorIndependentSetCharge_finsetClique_right
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {W : Set V} (K : Finset V)
    (hK : G.IsClique (K : Set V))
    (hKW : ∀ j ∈ K, j ∉ W)
    (k : Nat) :
    G.operatorIndependentSetCharge M W (k + 1) =
      G.operatorIndependentSetCharge M (W ∪ (K : Set V)) (k + 1) +
        ∑ j ∈ K,
          G.operatorIndependentSetCharge M
              (W ∪ G.closedNeighborhood j) k * M.term j := by
  rw [operatorIndependentSetCharge_finsetClique M K hK hKW k]
  congr 1
  apply Finset.sum_congr rfl
  intro j hjK
  exact (operatorIndependentSetCharge_commutes_term_closedNeighborhood
    M W j k).symm

/-- Set-valued clique form of Eq. (50) in the right multiplication orientation
used in D21 of manuscript Lemma 17. -/
theorem operatorIndependentSetCharge_clique_right
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {K : Set V} (hK : G.IsClique K)
    (k : Nat) :
    G.operatorIndependentSetChargeFull M (k + 1) =
      G.operatorIndependentSetCharge M K (k + 1) +
        ∑ j ∈ verticesOfSet K,
          G.operatorIndependentSetCharge M
              (G.closedNeighborhood j) k * M.term j := by
  classical
  have hFiniteClique : G.IsClique (((verticesOfSet K : Finset V) : Set V)) := by
    intro a ha b hb hab
    exact hK (mem_verticesOfSet.mp ha) (mem_verticesOfSet.mp hb) hab
  have hAvoid : ∀ j ∈ verticesOfSet K, j ∉ (∅ : Set V) := by
    intro j hj
    simp
  have hVertices : (((verticesOfSet K : Finset V) : Set V)) = K := by
    ext v
    simp
  have h :=
    operatorIndependentSetCharge_finsetClique_right
      M (W := (∅ : Set V)) (verticesOfSet K)
        hFiniteClique hAvoid k
  rw [hVertices] at h
  simpa [operatorIndependentSetChargeFull] using h

end SimpleGraph
