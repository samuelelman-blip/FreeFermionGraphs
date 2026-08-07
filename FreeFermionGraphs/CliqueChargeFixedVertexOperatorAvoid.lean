import FreeFermionGraphs.CliqueChargeFixedVertexOperator

/-!
# Fixed-vertex operator identity with prior deletions

Eq. (50) is used twice in the proof of manuscript Lemma 17.  The second use
occurs after deleting `K_j`, so we need the fixed-vertex reindexing with an
arbitrary previously deleted carrier `W`.
-/

open Set
open scoped BigOperators

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- Independent `(k+1)`-sets avoiding `W` and containing `j`. -/
noncomputable def independentFinsetsContainingAvoid
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (W : Set V) (j : V) (k : Nat) : Finset (Finset V) := by
  classical
  exact (G.independentFinsetsOfCardAvoid W (k + 1)).filter fun S => j ∈ S

@[simp]
theorem mem_independentFinsetsContainingAvoid
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {W : Set V} {j : V} {k : Nat} {S : Finset V} :
    S ∈ G.independentFinsetsContainingAvoid W j k ↔
      S.card = k + 1 ∧
        G.IsIndepSet (S : Set V) ∧
        (∀ v ∈ S, v ∉ W) ∧
        j ∈ S := by
  classical
  constructor
  · intro hS
    rw [independentFinsetsContainingAvoid, Finset.mem_filter] at hS
    rw [mem_independentFinsetsOfCardAvoid] at hS
    exact ⟨hS.1.1, hS.1.2.1, hS.1.2.2, hS.2⟩
  · rintro ⟨hcard, hind, havoid, hjS⟩
    rw [independentFinsetsContainingAvoid, Finset.mem_filter]
    constructor
    · rw [mem_independentFinsetsOfCardAvoid]
      exact ⟨hcard, hind, havoid⟩
    · exact hjS

/-- Generalized fixed-vertex reindexing: after deleting `W`, configurations
containing `j` are obtained by inserting `j` into configurations avoiding
`W ∪ Γ[j]`. -/
theorem independentFinsetsContainingAvoid_eq_image
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {W : Set V} {j : V} (hjW : j ∉ W) (k : Nat) :
    G.independentFinsetsContainingAvoid W j k =
      (G.independentFinsetsOfCardAvoid
        (W ∪ G.closedNeighborhood j) k).image (fun T => insert j T) := by
  classical
  ext S
  constructor
  · intro hS
    rw [mem_independentFinsetsContainingAvoid] at hS
    have hEraseMem :
        S.erase j ∈ G.independentFinsetsOfCardAvoid
          (W ∪ G.closedNeighborhood j) k := by
      rw [mem_independentFinsetsOfCardAvoid]
      refine ⟨card_erase_eq_of_card_succ hS.2.2.2 hS.1,
        isIndepSet_erase hS.2.1, ?_⟩
      intro v hvErase hvUnion
      rcases hvUnion with hvW | hvClosed
      · exact hS.2.2.1 v (Finset.mem_of_mem_erase hvErase) hvW
      · exact erase_avoids_closedNeighborhood
          hS.2.1 hS.2.2.2 v hvErase hvClosed
    rw [Finset.mem_image]
    exact ⟨S.erase j, hEraseMem, Finset.insert_erase hS.2.2.2⟩
  · intro hS
    rw [Finset.mem_image] at hS
    rcases hS with ⟨T, hT, hTS⟩
    rw [mem_independentFinsetsOfCardAvoid] at hT
    have hjClosed : j ∈ G.closedNeighborhood j := by
      simp [closedNeighborhood]
    have hjNotT : j ∉ T := by
      intro hjT
      exact hT.2.2 j hjT (Or.inr hjClosed)
    have hAvoidClosed : ∀ v ∈ T, v ∉ G.closedNeighborhood j := by
      intro v hvT hvClosed
      exact hT.2.2 v hvT (Or.inr hvClosed)
    have hInsertIndependent :
        G.IsIndepSet (((insert j T : Finset V) : Set V)) :=
      isIndepSet_insert_of_avoids_closedNeighborhood hT.2.1 hAvoidClosed
    rw [mem_independentFinsetsContainingAvoid]
    subst S
    refine ⟨?_, hInsertIndependent, ?_, Finset.mem_insert_self j T⟩
    · simp [hjNotT, hT.1]
    · intro v hv
      rw [Finset.mem_insert] at hv
      rcases hv with hvj | hvT
      · simpa [hvj] using hjW
      · intro hvW
        exact hT.2.2 v hvT (Or.inl hvW)

/-- The generalized `j`-th operator contribution to Eq. (50):

`∑_{S ∋ j, S ∩ W = ∅} h_S = h_j Q_{G\(W∪Γ[j])}^(k)`.
-/
theorem sum_independentFinsetsContainingAvoid_eq_term_mul_charge
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    {W : Set V} {j : V} (hjW : j ∉ W) (k : Nat) :
    (∑ S ∈ G.independentFinsetsContainingAvoid W j k,
      M.independentProduct S) =
      M.term j * G.operatorIndependentSetCharge M
        (W ∪ G.closedNeighborhood j) k := by
  classical
  rw [independentFinsetsContainingAvoid_eq_image hjW]
  unfold operatorIndependentSetCharge
  let F := G.independentFinsetsOfCardAvoid
    (W ∪ G.closedNeighborhood j) k
  have hinj :
      ∀ T₁ ∈ F, ∀ T₂ ∈ F,
        insert j T₁ = insert j T₂ → T₁ = T₂ := by
    intro T₁ hT₁ T₂ hT₂ hEq
    rw [mem_independentFinsetsOfCardAvoid] at hT₁ hT₂
    apply insert_injective_on_avoids_closedNeighborhood
    · intro v hvT hvClosed
      exact hT₁.2.2 v hvT (Or.inr hvClosed)
    · intro v hvT hvClosed
      exact hT₂.2.2 v hvT (Or.inr hvClosed)
    · exact hEq
  rw [Finset.sum_image hinj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [mem_independentFinsetsOfCardAvoid] at hT
  apply independentProduct_insert_of_avoids_closedNeighborhood M hT.2.1
  intro v hvT hvClosed
  exact hT.2.2 v hvT (Or.inr hvClosed)

end SimpleGraph
