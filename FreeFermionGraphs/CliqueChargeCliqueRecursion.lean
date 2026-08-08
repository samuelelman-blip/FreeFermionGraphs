import FreeFermionGraphs.CliqueChargeSingleVertexRecursion

/-!
# Clique charge recursion, Eq. (50)

This module assembles the single-vertex recursion into the manuscript clique
recursion.  We first prove a finite-clique form with an arbitrary previously
deleted carrier `W`, then specialize to an arbitrary set-valued clique.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- Finite-clique form of Eq. (50), with an arbitrary previously deleted
carrier `W`.

For a clique `K`, no independent set contains more than one vertex of `K`, so
successive applications of the single-vertex recursion telescope without
changing the closed-neighborhood deletion attached to the remaining clique
vertices.
-/
theorem operatorIndependentSetCharge_finsetClique
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
          M.term j *
            G.operatorIndependentSetCharge M
              (W ∪ G.closedNeighborhood j) k := by
  classical
  induction K using Finset.induction_on generalizing W with
  | empty =>
      simp
  | @insert j K hjK ih =>
      have hjW : j ∉ W := hKW j (by simp)
      have hKrest : G.IsClique (K : Set V) := by
        intro a ha b hb hab
        exact hK (by simp [ha]) (by simp [hb]) hab
      have hRestAvoid : ∀ l ∈ K, l ∉ W ∪ ({j} : Set V) := by
        intro l hl hUnion
        rcases hUnion with hlW | hlj
        · exact hKW l (by simp [hl]) hlW
        · have hljEq : l = j := by simpa using hlj
          subst l
          exact hjK hl
      have hSingle :=
        operatorIndependentSetCharge_singleVertex
          M (W := W) (j := j) hjW k
      have hIH :=
        ih hKrest hRestAvoid (W := W ∪ ({j} : Set V))
      have hFinalDeletion :
          (W ∪ ({j} : Set V)) ∪ (K : Set V) =
            W ∪ ((insert j K : Finset V) : Set V) := by
        ext v
        simp [or_left_comm, or_comm]
      have hNeighborhoodDeletion :
          ∀ l ∈ K,
            (W ∪ ({j} : Set V)) ∪ G.closedNeighborhood l =
              W ∪ G.closedNeighborhood l := by
        intro l hl
        have hlj : l ≠ j := by
          intro h
          subst l
          exact hjK hl
        have hadj : G.Adj l j :=
          hK (by simp [hl]) (by simp) hlj
        have hjClosed : j ∈ G.closedNeighborhood l := by
          exact Set.mem_insert_iff.mpr
            (Or.inr ((G.mem_neighborSet l j).mpr hadj))
        ext v
        constructor
        · intro hv
          rcases hv with (hvW | hvj) | hvClosed
          · exact Or.inl hvW
          · have hvEq : v = j := by simpa using hvj
            subst v
            exact Or.inr hjClosed
          · exact Or.inr hvClosed
        · intro hv
          rcases hv with hvW | hvClosed
          · exact Or.inl (Or.inl hvW)
          · exact Or.inr hvClosed
      rw [hSingle, hIH, hFinalDeletion]
      have hsum :
          (∑ l ∈ K,
            M.term l *
              G.operatorIndependentSetCharge M
                ((W ∪ ({j} : Set V)) ∪ G.closedNeighborhood l) k) =
          ∑ l ∈ K,
            M.term l *
              G.operatorIndependentSetCharge M
                (W ∪ G.closedNeighborhood l) k := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hNeighborhoodDeletion l hl]
      rw [hsum]
      simp [Finset.sum_insert, hjK]
      ac_rfl

/-- Manuscript Eq. (50), specialized to a set-valued clique `K`.

In manuscript notation this is

`Q_G^(k+1) = Q_{G\K}^(k+1) + ∑_{j∈K} h_j Q_{G\Γ[j]}^k`.

The finite representative `verticesOfSet K` is only an implementation device
for the finite sum over the clique.
-/
theorem operatorIndependentSetCharge_clique
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {K : Set V} (hK : G.IsClique K)
    (k : Nat) :
    G.operatorIndependentSetChargeFull M (k + 1) =
      G.operatorIndependentSetCharge M K (k + 1) +
        ∑ j ∈ verticesOfSet K,
          M.term j *
            G.operatorIndependentSetCharge M
              (G.closedNeighborhood j) k := by
  classical
  have hVertices : (((verticesOfSet K : Finset V) : Set V)) = K := by
    ext v
    simp
  have hFiniteClique : G.IsClique (((verticesOfSet K : Finset V) : Set V)) := by
    rw [hVertices]
    exact hK
  have hAvoid : ∀ j ∈ verticesOfSet K, j ∉ (∅ : Set V) := by
    intro j hj
    simp
  have h :=
    operatorIndependentSetCharge_finsetClique
      M (W := (∅ : Set V)) (verticesOfSet K)
        hFiniteClique hAvoid k
  rw [hVertices] at h
  simpa [operatorIndependentSetChargeFull] using h

end SimpleGraph
