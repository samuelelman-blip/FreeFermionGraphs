import FreeFermionGraphs.Lemma17PairCancellation

/-!
# Lemma 17: cancellation of the ordered double sum in (D24)

The final obstruction term in manuscript equation (D24) is a sum over ordered
pairs of distinct vertices of the simplicial clique.  Swapping the two indices
is a fixed-point-free involution of that finite index set, and the two
corresponding operator contributions cancel by `lemma17_orderedPair_cancel`.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- Ordered pairs of distinct vertices of a set-valued clique. -/
noncomputable def lemma17OrderedPairs
    [Fintype V] [DecidableEq V] (Ks : Set V) : Finset (V × V) := by
  classical
  exact ((verticesOfSet Ks).product (verticesOfSet Ks)).filter
    (fun p => p.1 ≠ p.2)

@[simp]
theorem mem_lemma17OrderedPairs
    [Fintype V] [DecidableEq V]
    {Ks : Set V} {p : V × V} :
    p ∈ lemma17OrderedPairs Ks ↔
      p.1 ∈ Ks ∧ p.2 ∈ Ks ∧ p.1 ≠ p.2 := by
  classical
  rcases p with ⟨j, k⟩
  simp [lemma17OrderedPairs, and_assoc]

/-- The ordered-pair contribution appearing in the third term of (D24). -/
noncomputable def lemma17OrderedPairContribution
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    (Ks : Set V) (n : Nat) (p : V × V) : A :=
  (G.operatorIndependentSetCharge M
      (Ks ∪ G.lemma17CliqueAt Ks p.1 ∪ G.lemma17CliqueAt Ks p.2) n *
        M.term p.2) * M.term p.1

/-- The entire ordered double sum in manuscript equation (D24) vanishes.

The involution `(j,k) ↦ (k,j)` preserves the index set, has no fixed points
because only distinct pairs are included, and its two contributions cancel by
anticommutation of the clique terms. -/
theorem lemma17_orderedDoubleSum_eq_zero
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    (n : Nat) :
    ∑ p ∈ lemma17OrderedPairs Ks,
      lemma17OrderedPairContribution M Ks n p = 0 := by
  classical
  let s := lemma17OrderedPairs Ks
  let f : V × V → A := lemma17OrderedPairContribution M Ks n
  have hsum : s.sum f = 0 := by
    refine Finset.sum_involution
      (s := s) (f := f)
      (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      have hp' : p ∈ lemma17OrderedPairs Ks := by
        simpa [s] using hp
      have hpMem := mem_lemma17OrderedPairs.mp hp'
      rcases p with ⟨j, k⟩
      change f (j, k) + f (k, j) = 0
      change
        lemma17OrderedPairContribution M Ks n (j, k) +
          lemma17OrderedPairContribution M Ks n (k, j) = 0
      exact lemma17_orderedPair_cancel M hKs hpMem.1 hpMem.2.1 hpMem.2.2 n
    · intro p hp _hf
      have hp' : p ∈ lemma17OrderedPairs Ks := by
        simpa [s] using hp
      have hpMem := mem_lemma17OrderedPairs.mp hp'
      intro hswap
      have hfst : p.2 = p.1 := congrArg Prod.fst hswap
      exact hpMem.2.2 hfst.symm
    · intro p hp
      have hp' : p ∈ lemma17OrderedPairs Ks := by
        simpa [s] using hp
      have hpMem := mem_lemma17OrderedPairs.mp hp'
      have hswap : (p.2, p.1) ∈ lemma17OrderedPairs Ks := by
        apply mem_lemma17OrderedPairs.mpr
        exact ⟨hpMem.2.1, hpMem.1, Ne.symm hpMem.2.2⟩
      simpa [s] using hswap
    · intro p hp
      simp
  simpa [s, f, lemma17OrderedPairContribution] using hsum

end SimpleGraph
