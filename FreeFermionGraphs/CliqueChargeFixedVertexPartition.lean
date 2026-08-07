import FreeFermionGraphs.CliqueChargeConfigurationEquiv

/-!
# Fixed-vertex partition for Eq. (50)

This module records the finite-set identity behind the `j`-th summand of the
clique recursion Eq. (50): independent `(k+1)`-sets containing `j` are exactly
obtained by inserting `j` into independent `k`-sets avoiding the closed
neighborhood `Γ[j]`.
-/

open Set

universe u
variable {V : Type u}

namespace SimpleGraph

/-- The finite family of independent `(k+1)`-sets containing `j`. -/
noncomputable def independentFinsetsContaining
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (j : V) (k : Nat) : Finset (Finset V) := by
  classical
  exact (G.independentFinsetsOfCardAvoid ∅ (k + 1)).filter fun S => j ∈ S

@[simp]
theorem mem_independentFinsetsContaining
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {j : V} {k : Nat} {S : Finset V} :
    S ∈ G.independentFinsetsContaining j k ↔
      S.card = k + 1 ∧ G.IsIndepSet (S : Set V) ∧ j ∈ S := by
  classical
  rw [independentFinsetsContaining, Finset.mem_filter,
    mem_independentFinsetsOfCardAvoid]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2.1, h.2⟩
  · intro h
    refine ⟨⟨h.1, h.2.1, ?_⟩, h.2.2⟩
    intro v hvS hvEmpty
    exact hvEmpty

/-- Fixed-vertex reindexing used in Eq. (50).

The right-hand side is the image of the independent `k`-sets of
`G \ Γ[j]` under insertion of `j`. -/
theorem independentFinsetsContaining_eq_image_closedNeighborhood
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    (j : V) (k : Nat) :
    G.independentFinsetsContaining j k =
      (G.independentFinsetsOfCardAvoid (G.closedNeighborhood j) k).image
        (fun T => insert j T) := by
  classical
  ext S
  constructor
  · intro hS
    rw [mem_independentFinsetsContaining] at hS
    have hEraseMem :
        S.erase j ∈
          G.independentFinsetsOfCardAvoid (G.closedNeighborhood j) k := by
      rw [mem_independentFinsetsOfCardAvoid]
      refine ⟨card_erase_eq_of_card_succ hS.2.2 hS.1,
        isIndepSet_erase hS.2.1, ?_⟩
      exact erase_avoids_closedNeighborhood hS.2.1 hS.2.2
    rw [Finset.mem_image]
    exact ⟨S.erase j, hEraseMem, Finset.insert_erase hS.2.2⟩
  · intro hS
    rw [Finset.mem_image] at hS
    rcases hS with ⟨T, hT, hTS⟩
    rw [mem_independentFinsetsOfCardAvoid] at hT
    have hjClosed : j ∈ G.closedNeighborhood j := by
      simp [closedNeighborhood]
    have hjNotT : j ∉ T := by
      intro hjT
      exact hT.2.2 j hjT hjClosed
    have hAvoidClosed : ∀ v ∈ T, v ∉ G.closedNeighborhood j := hT.2.2
    have hInsertIndependent :
        G.IsIndepSet (((insert j T : Finset V) : Set V)) :=
      isIndepSet_insert_of_avoids_closedNeighborhood hT.2.1 hAvoidClosed
    rw [mem_independentFinsetsContaining]
    subst S
    refine ⟨?_, hInsertIndependent, Finset.mem_insert_self j T⟩
    simp [hjNotT, hT.1]

end SimpleGraph
