import FreeFermionGraphs.CliqueChargeFixedVertexPartition

/-!
# Fixed-vertex operator identity for Eq. (50)

This module turns the fixed-vertex configuration reindexing into the operator
identity used in Eq. (50). For a fixed vertex `j`, the sum over independent
`(k+1)`-sets containing `j` is `h_j` times the `k`-charge on the graph with
`Γ[j]` deleted.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- Inserting `j` into an independent set that avoids `Γ[j]` gives the
manuscript product `h_j h_T`. -/
theorem independentProduct_insert_of_avoids_closedNeighborhood
    {G : SimpleGraph V} [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {j : V} {T : Finset V}
    (hTind : G.IsIndepSet (T : Set V))
    (hTavoid : ∀ v ∈ T, v ∉ G.closedNeighborhood j) :
    M.independentProduct (insert j T) =
      M.term j * M.independentProduct T := by
  have hjNotT : j ∉ T := by
    intro hjT
    have hjClosed : j ∈ G.closedNeighborhood j := by
      simp [closedNeighborhood]
    exact hTavoid j hjT hjClosed
  apply M.independentProduct_insert_left hjNotT hTind
  intro v hvT hadj
  apply hTavoid v hvT
  exact Set.mem_insert_iff.mpr
    (Or.inr ((G.mem_neighborSet j v).mpr hadj))

/-- The insertion map is injective on configurations avoiding `Γ[j]`. -/
theorem insert_injective_on_avoids_closedNeighborhood
    {G : SimpleGraph V} [DecidableEq V]
    {j : V} {T₁ T₂ : Finset V}
    (hT₁ : ∀ v ∈ T₁, v ∉ G.closedNeighborhood j)
    (hT₂ : ∀ v ∈ T₂, v ∉ G.closedNeighborhood j)
    (h : insert j T₁ = insert j T₂) :
    T₁ = T₂ := by
  have hjNotT₁ : j ∉ T₁ := by
    intro hjT
    exact hT₁ j hjT (by simp [closedNeighborhood])
  have hjNotT₂ : j ∉ T₂ := by
    intro hjT
    exact hT₂ j hjT (by simp [closedNeighborhood])
  have hErase := congrArg (fun S : Finset V => S.erase j) h
  simpa [hjNotT₁, hjNotT₂] using hErase

/-- The `j`-th operator contribution in Eq. (50).

This is the exact operator-valued version of the fixed-vertex reindexing:

`∑_{S ∋ j, |S| = k+1} h_S = h_j Q_{G\Γ[j]}^(k)`.
-/
theorem sum_independentFinsetsContaining_eq_term_mul_charge
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    (j : V) (k : Nat) :
    (∑ S ∈ G.independentFinsetsContaining j k,
      M.independentProduct S) =
      M.term j *
        G.operatorIndependentSetCharge M (G.closedNeighborhood j) k := by
  classical
  rw [independentFinsetsContaining_eq_image_closedNeighborhood]
  unfold operatorIndependentSetCharge
  let F := G.independentFinsetsOfCardAvoid (G.closedNeighborhood j) k
  have hinj :
      ∀ T₁ ∈ F, ∀ T₂ ∈ F,
        insert j T₁ = insert j T₂ → T₁ = T₂ := by
    intro T₁ hT₁ T₂ hT₂ hEq
    rw [mem_independentFinsetsOfCardAvoid] at hT₁ hT₂
    exact insert_injective_on_avoids_closedNeighborhood
      hT₁.2.2 hT₂.2.2 hEq
  rw [Finset.sum_image hinj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [mem_independentFinsetsOfCardAvoid] at hT
  exact independentProduct_insert_of_avoids_closedNeighborhood
    M hT.2.1 hT.2.2

end SimpleGraph
