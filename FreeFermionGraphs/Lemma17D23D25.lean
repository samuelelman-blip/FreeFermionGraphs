import FreeFermionGraphs.Lemma17DoubleSumCancellation

/-!
# Lemma 17: equations (D23)--(D25)

This module substitutes the fixed-vertex recursion (D22) into (D21), rewrites
the resulting nested sum as the ordered-pair sum of (D24), and then applies the
ordered-pair cancellation proved in `Lemma17DoubleSumCancellation`.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- The ordered-pair finset is the finite dependent product of a first vertex
`j ∈ Ks` and a second vertex `l ∈ Ks \ {j}`.  This is the precise reindexing
needed to identify the nested sum obtained from repeated use of (D22) with the
ordered double sum in (D24). -/
theorem lemma17_orderedDoubleSum_eq_nested
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    (Ks : Set V) (n : Nat) :
    (∑ p ∈ lemma17OrderedPairs Ks,
      lemma17OrderedPairContribution M Ks n p) =
      ∑ j ∈ verticesOfSet Ks,
        ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
          lemma17OrderedPairContribution M Ks n (j, l) := by
  classical
  have hmem :
      ∀ p : V × V,
        p ∈ lemma17OrderedPairs Ks ↔
          p.1 ∈ verticesOfSet Ks ∧
            p.2 ∈ verticesOfSet (Ks \ ({p.1} : Set V)) := by
    intro p
    rcases p with ⟨j, l⟩
    rw [mem_lemma17OrderedPairs]
    constructor
    · rintro ⟨hj, hl, hjl⟩
      refine ⟨mem_verticesOfSet.mpr hj, ?_⟩
      apply mem_verticesOfSet.mpr
      refine ⟨hl, ?_⟩
      simpa using (Ne.symm hjl)
    · rintro ⟨hjFin, hlFin⟩
      have hj : j ∈ Ks := mem_verticesOfSet.mp hjFin
      have hlRest : l ∈ Ks \ ({j} : Set V) :=
        mem_verticesOfSet.mp hlFin
      have hjl : j ≠ l := by
        intro h
        subst l
        exact hlRest.2 (by simp)
      exact ⟨hj, hlRest.1, hjl⟩
  simpa using
    (Finset.sum_finset_product
      (lemma17OrderedPairs Ks)
      (verticesOfSet Ks)
      (fun j => verticesOfSet (Ks \ ({j} : Set V)))
      hmem
      (f := fun p => lemma17OrderedPairContribution M Ks n p))

/-- The pointwise substitution used in (D23): solve (D22) for the charge on
`G \ (Ks ∪ K_j)` and multiply on the right by `h_j`. -/
theorem lemma17_D23_term
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    {j : V} (hj : j ∈ Ks)
    (n : Nat) :
    G.operatorIndependentSetCharge M
        (Ks ∪ G.lemma17CliqueAt Ks j) (n + 1) * M.term j =
      G.operatorIndependentSetCharge M
          (G.lemma17CliqueAt Ks j) (n + 1) * M.term j -
        ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
          lemma17OrderedPairContribution M Ks n (j, l) := by
  classical
  have hD22 := lemma17_D22 M hKs hj n
  have hsolve :
      G.operatorIndependentSetCharge M
          (Ks ∪ G.lemma17CliqueAt Ks j) (n + 1) =
        G.operatorIndependentSetCharge M
            (G.lemma17CliqueAt Ks j) (n + 1) -
          ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
            G.operatorIndependentSetCharge M
                (Ks ∪ G.lemma17CliqueAt Ks j ∪
                  G.lemma17CliqueAt Ks l) n * M.term l := by
    calc
      G.operatorIndependentSetCharge M
          (Ks ∪ G.lemma17CliqueAt Ks j) (n + 1) =
        (G.operatorIndependentSetCharge M
            (Ks ∪ G.lemma17CliqueAt Ks j) (n + 1) +
          ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
            G.operatorIndependentSetCharge M
                (Ks ∪ G.lemma17CliqueAt Ks j ∪
                  G.lemma17CliqueAt Ks l) n * M.term l) -
          ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
            G.operatorIndependentSetCharge M
                (Ks ∪ G.lemma17CliqueAt Ks j ∪
                  G.lemma17CliqueAt Ks l) n * M.term l := by simp
      _ = G.operatorIndependentSetCharge M
            (G.lemma17CliqueAt Ks j) (n + 1) -
          ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
            G.operatorIndependentSetCharge M
                (Ks ∪ G.lemma17CliqueAt Ks j ∪
                  G.lemma17CliqueAt Ks l) n * M.term l := by
        rw [← hD22]
  rw [hsolve, sub_mul, Finset.sum_mul]
  simp [lemma17OrderedPairContribution]

/-- Manuscript equation (D23), with the original charge degree written as
`n + 2`. -/
theorem lemma17_D23
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    (n : Nat) :
    G.operatorIndependentSetChargeFull M (n + 2) =
      G.operatorIndependentSetCharge M Ks (n + 2) +
        (∑ j ∈ verticesOfSet Ks,
          G.operatorIndependentSetCharge M
              (G.lemma17CliqueAt Ks j) (n + 1) * M.term j) -
        ∑ p ∈ lemma17OrderedPairs Ks,
          lemma17OrderedPairContribution M Ks n p := by
  classical
  have hD21 := lemma17_D21 M hKs (n + 1)
  have hsum :
      (∑ j ∈ verticesOfSet Ks,
        G.operatorIndependentSetCharge M
            (Ks ∪ G.lemma17CliqueAt Ks j) (n + 1) * M.term j) =
        (∑ j ∈ verticesOfSet Ks,
          G.operatorIndependentSetCharge M
              (G.lemma17CliqueAt Ks j) (n + 1) * M.term j) -
          ∑ p ∈ lemma17OrderedPairs Ks,
            lemma17OrderedPairContribution M Ks n p := by
    calc
      (∑ j ∈ verticesOfSet Ks,
        G.operatorIndependentSetCharge M
            (Ks ∪ G.lemma17CliqueAt Ks j) (n + 1) * M.term j) =
        ∑ j ∈ verticesOfSet Ks,
          (G.operatorIndependentSetCharge M
              (G.lemma17CliqueAt Ks j) (n + 1) * M.term j -
            ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
              lemma17OrderedPairContribution M Ks n (j, l)) := by
        apply Finset.sum_congr rfl
        intro j hjFin
        exact lemma17_D23_term M hKs (mem_verticesOfSet.mp hjFin) n
      _ = (∑ j ∈ verticesOfSet Ks,
          G.operatorIndependentSetCharge M
              (G.lemma17CliqueAt Ks j) (n + 1) * M.term j) -
          ∑ j ∈ verticesOfSet Ks,
            ∑ l ∈ verticesOfSet (Ks \ ({j} : Set V)),
              lemma17OrderedPairContribution M Ks n (j, l) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ j ∈ verticesOfSet Ks,
          G.operatorIndependentSetCharge M
              (G.lemma17CliqueAt Ks j) (n + 1) * M.term j) -
          ∑ p ∈ lemma17OrderedPairs Ks,
            lemma17OrderedPairContribution M Ks n p := by
        rw [lemma17_orderedDoubleSum_eq_nested M Ks n]
  rw [hsum] at hD21
  simpa [Nat.add_assoc, sub_eq_add_neg, add_assoc] using hD21

/-- Manuscript equation (D25), and hence the Lemma 17 recursion, for charge
orders at least two.  The remaining ordered-pair term in (D23)/(D24) vanishes
by the swap cancellation. -/
theorem lemma17_D25_succ_succ
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    (n : Nat) :
    G.operatorIndependentSetChargeFull M (n + 2) =
      G.operatorIndependentSetCharge M Ks (n + 2) +
        ∑ j ∈ verticesOfSet Ks,
          G.operatorIndependentSetCharge M
              (G.lemma17CliqueAt Ks j) (n + 1) * M.term j := by
  have h := lemma17_D23 M hKs n
  have hcancel := lemma17_orderedDoubleSum_eq_zero M hKs n
  rw [hcancel] at h
  simpa using h

end SimpleGraph
