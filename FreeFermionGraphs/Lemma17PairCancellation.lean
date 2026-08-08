import FreeFermionGraphs.Lemma17D21D22

/-!
# Lemma 17: pairwise cancellation in (D24)

The third term in manuscript equation (D24) is indexed by ordered pairs of
distinct vertices of the simplicial clique.  Its coefficient is symmetric
under interchanging the two clique vertices, while the two Hamiltonian terms
anticommute.  This module isolates that literal two-term cancellation.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- The deleted carrier appearing in the coefficient of the `(j,k)` term of
(D24) is symmetric under swapping `j` and `k`. -/
theorem lemma17_doubleDeletion_symm
    {G : SimpleGraph V} {Ks : Set V} (j k : V) :
    Ks ∪ G.lemma17CliqueAt Ks j ∪ G.lemma17CliqueAt Ks k =
      Ks ∪ G.lemma17CliqueAt Ks k ∪ G.lemma17CliqueAt Ks j := by
  ext v
  constructor
  · intro hv
    rcases hv with (hvKs | hvKj) | hvKk
    · exact Or.inl (Or.inl hvKs)
    · exact Or.inr hvKj
    · exact Or.inl (Or.inr hvKk)
  · intro hv
    rcases hv with (hvKs | hvKk) | hvKj
    · exact Or.inl (Or.inl hvKs)
    · exact Or.inr hvKk
    · exact Or.inl (Or.inr hvKj)

/-- The two ordered contributions associated with `(j,k)` and `(k,j)` in
(D24) cancel exactly.

The coefficient is the same after swapping the two indices by
`lemma17_doubleDeletion_symm`; anticommutation follows because distinct
vertices of the simplicial clique are adjacent in the frustration graph. -/
theorem lemma17_orderedPair_cancel
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    {j k : V} (hj : j ∈ Ks) (hk : k ∈ Ks) (hjk : j ≠ k)
    (n : Nat) :
    (G.operatorIndependentSetCharge M
        (Ks ∪ G.lemma17CliqueAt Ks j ∪ G.lemma17CliqueAt Ks k) n *
          M.term k) * M.term j +
      (G.operatorIndependentSetCharge M
        (Ks ∪ G.lemma17CliqueAt Ks k ∪ G.lemma17CliqueAt Ks j) n *
          M.term j) * M.term k = 0 := by
  have hdel := lemma17_doubleDeletion_symm (G := G) (Ks := Ks) j k
  rw [hdel]
  have hkj : k ≠ j := Ne.symm hjk
  have hadj : G.Adj k j := hKs.isClique hk hj hkj
  have hanti := M.anticommute_of_adj hadj
  rw [mul_assoc, mul_assoc, hanti]
  simp

end SimpleGraph
