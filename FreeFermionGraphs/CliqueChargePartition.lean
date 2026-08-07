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

theorem independent_clique_filter_card_le_one
    [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {K : Set V}
    (hS : G.IsIndepSet (S : Set V)) (hK : G.IsClique K) :
    (S.filter fun v => v ∈ K).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j hj k hk
  simp only [Finset.mem_filter] at hj hk
  exact independent_clique_mem_eq hS hK hj.1 hj.2 hk.1 hk.2

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
    simpa using hvErase
  rcases Set.mem_insert_iff.mp hvClosed with hvj | hvNeighbor
  · exact hvne hvj
  · have hadj : G.Adj j v := (G.mem_neighborSet j v).mp hvNeighbor
    exact (hS hj hvS hvne.symm) hadj

end SimpleGraph
