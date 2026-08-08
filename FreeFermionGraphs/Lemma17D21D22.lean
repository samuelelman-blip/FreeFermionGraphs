import FreeFermionGraphs.CliqueChargeRightOrientation

/-!
# Lemma 17: equations (D21) and (D22)

This module specializes the right-oriented clique recursion to the simplicial
clique `Ks` and to the auxiliary cliques

`K_j = Γ[j] \ (Ks \ {j})`.

The two resulting identities are exactly the first two recursive expansions in
the manuscript proof of Lemma 17.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- Manuscript equation (D21), with degree written as `n + 1` so that no
truncated natural-number subtraction appears in the formal statement. -/
theorem lemma17_D21
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    (n : Nat) :
    G.operatorIndependentSetChargeFull M (n + 1) =
      G.operatorIndependentSetCharge M Ks (n + 1) +
        ∑ j ∈ verticesOfSet Ks,
          G.operatorIndependentSetCharge M
              (Ks ∪ G.lemma17CliqueAt Ks j) n * M.term j := by
  rw [operatorIndependentSetCharge_clique_right M hKs.isClique n]
  congr 1
  apply Finset.sum_congr rfl
  intro j hjFin
  have hj : j ∈ Ks := mem_verticesOfSet.mp hjFin
  rw [← closedNeighborhood_eq_union_lemma17CliqueAt hKs hj]

/-- The finite representative of `Ks \ {j}` is exactly that set. -/
theorem coe_verticesOfSet_diff_singleton
    [Fintype V] [DecidableEq V]
    (Ks : Set V) (j : V) :
    (((verticesOfSet (Ks \ ({j} : Set V)) : Finset V) : Set V)) =
      Ks \ ({j} : Set V) := by
  ext v
  simp

/-- A simplicial-clique vertex belongs to its auxiliary clique `K_j`. -/
theorem mem_lemma17CliqueAt_self
    {G : SimpleGraph V} {Ks : Set V} {j : V}
    (hj : j ∈ Ks) :
    j ∈ G.lemma17CliqueAt Ks j := by
  rw [lemma17CliqueAt_eq_insert_external hj]
  simp

/-- Deleting `K_j` and then the remaining simplicial-clique vertices is the
same as deleting `Ks ∪ K_j`. -/
theorem lemma17CliqueAt_union_diff_singleton
    {G : SimpleGraph V} {Ks : Set V} {j : V}
    (hj : j ∈ Ks) :
    G.lemma17CliqueAt Ks j ∪ (Ks \ ({j} : Set V)) =
      Ks ∪ G.lemma17CliqueAt Ks j := by
  ext v
  constructor
  · intro hv
    rcases hv with hvKj | hvRest
    · exact Or.inr hvKj
    · exact Or.inl hvRest.1
  · intro hv
    rcases hv with hvKs | hvKj
    · by_cases hvj : v = j
      · subst v
        exact Or.inl (mem_lemma17CliqueAt_self hj)
      · exact Or.inr ⟨hvKs, by simp [hvj]⟩
    · exact Or.inl hvKj

/-- Manuscript equation (D22), again with the degree shifted to avoid natural
subtraction.  For fixed `j ∈ Ks`, Eq. (50) is applied to the remaining clique
`Ks \ {j}` after `K_j` has already been deleted. -/
theorem lemma17_D22
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    {j : V} (hj : j ∈ Ks)
    (n : Nat) :
    G.operatorIndependentSetCharge M
        (G.lemma17CliqueAt Ks j) (n + 1) =
      G.operatorIndependentSetCharge M
          (Ks ∪ G.lemma17CliqueAt Ks j) (n + 1) +
        ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
          G.operatorIndependentSetCharge M
              (Ks ∪ G.lemma17CliqueAt Ks j ∪
                G.lemma17CliqueAt Ks l) n * M.term l := by
  classical
  let Krest : Finset V := verticesOfSet (Ks \ ({j} : Set V))
  have hKrestSet : ((Krest : Finset V) : Set V) =
      Ks \ ({j} : Set V) := by
    simpa [Krest] using coe_verticesOfSet_diff_singleton Ks j
  have hKrestClique : G.IsClique ((Krest : Finset V) : Set V) := by
    intro a ha b hb hab
    have haRest : a ∈ Ks \ ({j} : Set V) := by
      rw [hKrestSet] at ha
      exact ha
    have hbRest : b ∈ Ks \ ({j} : Set V) := by
      rw [hKrestSet] at hb
      exact hb
    exact hKs.isClique haRest.1 hbRest.1 hab
  have hKrestAvoid :
      ∀ l ∈ Krest, l ∉ G.lemma17CliqueAt Ks j := by
    intro l hl hlKj
    have hlRest : l ∈ Ks \ ({j} : Set V) := by
      have : l ∈ ((Krest : Finset V) : Set V) := hl
      rw [hKrestSet] at this
      exact this
    change l ∈ G.closedNeighborhood j \ (Ks \ ({j} : Set V)) at hlKj
    exact hlKj.2 hlRest
  have h :=
    operatorIndependentSetCharge_finsetClique_right
      M (W := G.lemma17CliqueAt Ks j) Krest
        hKrestClique hKrestAvoid n
  have hFinalDeletion :
      G.lemma17CliqueAt Ks j ∪ ((Krest : Finset V) : Set V) =
        Ks ∪ G.lemma17CliqueAt Ks j := by
    rw [hKrestSet]
    exact lemma17CliqueAt_union_diff_singleton hj
  have hNeighborhoodDeletion :
      ∀ l ∈ Krest,
        G.lemma17CliqueAt Ks j ∪ G.closedNeighborhood l =
          Ks ∪ G.lemma17CliqueAt Ks j ∪ G.lemma17CliqueAt Ks l := by
    intro l hl
    have hlRest : l ∈ Ks \ ({j} : Set V) := by
      have : l ∈ ((Krest : Finset V) : Set V) := hl
      rw [hKrestSet] at this
      exact this
    rw [closedNeighborhood_eq_union_lemma17CliqueAt hKs hlRest.1]
    ext v
    constructor
    · intro hv
      rcases hv with hvKj | hvRest
      · exact Or.inl (Or.inr hvKj)
      · rcases hvRest with hvKs | hvKl
        · exact Or.inl (Or.inl hvKs)
        · exact Or.inr hvKl
    · intro hv
      rcases hv with hvFirst | hvKl
      · rcases hvFirst with hvKs | hvKj
        · exact Or.inr (Or.inl hvKs)
        · exact Or.inl hvKj
      · exact Or.inr (Or.inr hvKl)
  rw [hFinalDeletion] at h
  have hsum :
      (∑ l ∈ Krest,
        G.operatorIndependentSetCharge M
            (G.lemma17CliqueAt Ks j ∪ G.closedNeighborhood l) n *
          M.term l) =
        ∑ l ∈ Krest,
          G.operatorIndependentSetCharge M
              (Ks ∪ G.lemma17CliqueAt Ks j ∪
                G.lemma17CliqueAt Ks l) n * M.term l := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [hNeighborhoodDeletion l hl]
  rw [hsum] at h
  simpa [Krest] using h

end SimpleGraph
