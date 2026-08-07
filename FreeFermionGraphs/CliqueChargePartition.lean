import FreeFermionGraphs.FrustrationOperator

/-!
# Clique partition of independent sets

Finite-set lemmas used to prove the operator charge recursion Eq. (50).
-/

open Set

universe u
variable {V : Type u}

namespace SimpleGraph

noncomputable def verticesOfSet [Fintype V] [DecidableEq V]
    (K : Set V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∈ K

@[simp] theorem mem_verticesOfSet [Fintype V] [DecidableEq V]
    {K : Set V} {v : V} : v ∈ verticesOfSet K ↔ v ∈ K := by
  classical
  simp [verticesOfSet]

theorem independent_clique_mem_eq
    {G : SimpleGraph V} {S : Finset V} {K : Set V}
    (hS : G.IsIndepSet (S : Set V)) (hK : G.IsClique K)
    {j k : V} (hjS : j ∈ S) (hjK : j ∈ K)
    (hkS : k ∈ S) (hkK : k ∈ K) : j = k := by
  by_contra hjk
  exact (hS hjS hkS hjk) (hK hjK hkK hjk)

/-- An independent set intersects a clique in at most one vertex.

The finite representative `verticesOfSet K` avoids requiring a decidable
membership predicate for the arbitrary set `K` in the theorem statement. -/
theorem independent_clique_inter_card_le_one
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {K : Set V}
    (hS : G.IsIndepSet (S : Set V)) (hK : G.IsClique K) :
    (S ∩ verticesOfSet K).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j hj k hk
  have hjS : j ∈ S := (Finset.mem_inter.mp hj).1
  have hjK : j ∈ K := by
    exact mem_verticesOfSet.mp (Finset.mem_inter.mp hj).2
  have hkS : k ∈ S := (Finset.mem_inter.mp hk).1
  have hkK : k ∈ K := by
    exact mem_verticesOfSet.mp (Finset.mem_inter.mp hk).2
  exact independent_clique_mem_eq hS hK hjS hjK hkS hkK

theorem card_erase_eq_of_card_succ
    [DecidableEq V]
    {S : Finset V} {j : V} {k : Nat}
    (hj : j ∈ S) (hcard : S.card = k + 1) :
    (S.erase j).card = k := by
  rw [Finset.card_erase_of_mem hj, hcard]
  omega

theorem isIndepSet_erase
    [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {j : V}
    (hS : G.IsIndepSet (S : Set V)) :
    G.IsIndepSet ((S.erase j : Finset V) : Set V) := by
  intro a ha b hb hab
  exact hS (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab

theorem erase_avoids_closedNeighborhood
    [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {j : V}
    (hS : G.IsIndepSet (S : Set V)) (hj : j ∈ S) :
    ∀ v ∈ S.erase j, v ∉ G.closedNeighborhood j := by
  intro v hvErase hvClosed
  have hvS : v ∈ S := Finset.mem_of_mem_erase hvErase
  have hvne : v ≠ j := by
    intro hvj
    subst v
    simp at hvErase
  rcases Set.mem_insert_iff.mp hvClosed with hvj | hvNeighbor
  · exact hvne hvj
  · have hadj : G.Adj j v := (G.mem_neighborSet j v).mp hvNeighbor
    exact (hS hj hvS hvne.symm) hadj

/-- Conversely, an independent set avoiding `Γ[j]` remains independent after
inserting `j`. This is the inverse combinatorial step in Eq. (50). -/
theorem isIndepSet_insert_of_avoids_closedNeighborhood
    [DecidableEq V]
    {G : SimpleGraph V} {T : Finset V} {j : V}
    (hT : G.IsIndepSet (T : Set V))
    (havoid : ∀ v ∈ T, v ∉ G.closedNeighborhood j) :
    G.IsIndepSet ((insert j T : Finset V) : Set V) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
  rcases ha with haJ | haT
  · rcases hb with hbJ | hbT
    · exact (hab (haJ.trans hbJ.symm)).elim
    · intro hadj
      apply havoid b hbT
      have hadj' : G.Adj j b := by
        simpa [haJ] using hadj
      exact Set.mem_insert_iff.mpr
        (Or.inr ((G.mem_neighborSet j b).mpr hadj'))
  · rcases hb with hbJ | hbT
    · intro hadj
      apply havoid a haT
      have hadj' : G.Adj j a := by
        have : G.Adj a j := by
          simpa [hbJ] using hadj
        exact this.symm
      exact Set.mem_insert_iff.mpr
        (Or.inr ((G.mem_neighborSet j a).mpr hadj'))
    · exact hT haT hbT hab

end SimpleGraph
