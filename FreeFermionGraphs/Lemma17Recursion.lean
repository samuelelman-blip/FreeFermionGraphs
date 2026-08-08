import FreeFermionGraphs.Lemma17D23D25

/-!
# Lemma 17: full positive-degree recursion

The manuscript recursion contains `Q^(k-1)`, so its natural-number formal
statement is for positive charge degree `k + 1`.  The D23--D25 cancellation
argument proves every degree at least two.  This module closes the remaining
degree-one case directly from Eq. (50), using that every degree-zero
independent-set charge is the identity.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- There is exactly one independent set of cardinality zero, namely the empty
set, independently of the deleted carrier. -/
theorem independentFinsetsOfCardAvoid_zero
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    (W : Set V) :
    G.independentFinsetsOfCardAvoid W 0 = {∅} := by
  classical
  ext S
  rw [mem_independentFinsetsOfCardAvoid]
  constructor
  · intro h
    rw [Finset.mem_singleton]
    exact Finset.card_eq_zero.mp h.1
  · intro h
    rw [Finset.mem_singleton] at h
    subst S
    exact ⟨by simp, by simp, by simp⟩

/-- The manuscript convention `Q^(0) = 1`, valid for every vertex-deleted
induced subgraph. -/
@[simp]
theorem operatorIndependentSetCharge_zero
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    (W : Set V) :
    G.operatorIndependentSetCharge M W 0 = 1 := by
  classical
  unfold operatorIndependentSetCharge
  rw [independentFinsetsOfCardAvoid_zero W]
  simp [M.independentProduct_empty]

/-- Lemma 17 at charge degree one.  At this degree both the closed-neighborhood
coefficient from Eq. (50) and the `K_j` coefficient in (D25) are `Q^(0) = 1`.
-/
theorem lemma17_D25_one
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks) :
    G.operatorIndependentSetChargeFull M 1 =
      G.operatorIndependentSetCharge M Ks 1 +
        ∑ j ∈ verticesOfSet Ks,
          G.operatorIndependentSetCharge M
              (G.lemma17CliqueAt Ks j) 0 * M.term j := by
  have h := operatorIndependentSetCharge_clique_right M hKs.isClique 0
  simpa using h

/-- Full positive-degree form of manuscript Lemma 17 at the audited operator
interface:

`Q_G^(k+1) = Q_(G\Ks)^(k+1) + ∑_{j∈Ks} Q_(G\K_j)^k h_j`,

where `K_j = Γ[j] \ (Ks \ {j})`.
-/
theorem lemma17_D25
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {Ks : Set V} (hKs : G.IsSimplicialClique Ks)
    (k : Nat) :
    G.operatorIndependentSetChargeFull M (k + 1) =
      G.operatorIndependentSetCharge M Ks (k + 1) +
        ∑ j ∈ verticesOfSet Ks,
          G.operatorIndependentSetCharge M
              (G.lemma17CliqueAt Ks j) k * M.term j := by
  cases k with
  | zero =>
      simpa using lemma17_D25_one M hKs
  | succ n =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        lemma17_D25_succ_succ M hKs n

end SimpleGraph
