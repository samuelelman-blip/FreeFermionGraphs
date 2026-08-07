import FreeFermionGraphs.CliqueChargePartition

/-!
# Configuration equivalence behind Eq. (50)

For a fixed clique vertex `j`, independent configurations containing `j` are
in bijection with one-smaller independent configurations avoiding the closed
neighborhood `Γ[j]`.  This is the reindexing used in the operator charge
recursion.
-/

open Set

universe u
variable {V : Type u}

namespace SimpleGraph

/-- A `k`-vertex independent configuration avoiding a deleted carrier `W`. -/
structure AvoidingIndependentConfiguration
    (G : SimpleGraph V) (W : Set V) (k : Nat) where
  carrier : Finset V
  card_eq : carrier.card = k
  independent : G.IsIndepSet (carrier : Set V)
  avoids : ∀ v ∈ carrier, v ∉ W

@[ext]
theorem AvoidingIndependentConfiguration.ext
    {G : SimpleGraph V} {W : Set V} {k : Nat}
    {S T : AvoidingIndependentConfiguration G W k}
    (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- A `(k+1)`-vertex independent configuration avoiding `W` and containing
one specified vertex `j`. -/
structure ContainingIndependentConfiguration
    (G : SimpleGraph V) (W : Set V) (j : V) (k : Nat) where
  carrier : Finset V
  card_eq : carrier.card = k + 1
  independent : G.IsIndepSet (carrier : Set V)
  avoids : ∀ v ∈ carrier, v ∉ W
  contains : j ∈ carrier

@[ext]
theorem ContainingIndependentConfiguration.ext
    {G : SimpleGraph V} {W : Set V} {j : V} {k : Nat}
    {S T : ContainingIndependentConfiguration G W j k}
    (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- Erasing `j` gives the exact bijection between configurations containing
`j` and configurations avoiding `W ∪ Γ[j]`.  The premise `j ∉ W` is the
literal condition needed when Eq. (50) is applied after earlier vertex
deletions. -/
noncomputable def eraseContainingEquiv
    [DecidableEq V]
    {G : SimpleGraph V} {W : Set V} {j : V}
    (hjW : j ∉ W) (k : Nat) :
    ContainingIndependentConfiguration G W j k ≃
      AvoidingIndependentConfiguration G
        (W ∪ G.closedNeighborhood j) k := by
  classical
  refine
    { toFun := fun S => ?_
      invFun := fun T => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine
      { carrier := S.carrier.erase j
        card_eq := card_erase_eq_of_card_succ S.contains S.card_eq
        independent := isIndepSet_erase S.independent
        avoids := ?_ }
    intro v hv
    intro hvUnion
    rcases hvUnion with hvW | hvClosed
    · exact S.avoids v (Finset.mem_of_mem_erase hv) hvW
    · exact erase_avoids_closedNeighborhood S.independent S.contains v hv hvClosed
  · have hjClosed : j ∈ G.closedNeighborhood j := by
      simp [closedNeighborhood]
    have hjNotT : j ∉ T.carrier := by
      intro hjT
      exact T.avoids j hjT (Or.inr hjClosed)
    have hAvoidClosed :
        ∀ v ∈ T.carrier, v ∉ G.closedNeighborhood j := by
      intro v hvT hvClosed
      exact T.avoids v hvT (Or.inr hvClosed)
    refine
      { carrier := insert j T.carrier
        card_eq := ?_
        independent :=
          isIndepSet_insert_of_avoids_closedNeighborhood
            T.independent hAvoidClosed
        avoids := ?_
        contains := Finset.mem_insert_self j T.carrier }
    · rw [Finset.card_insert_of_not_mem hjNotT, T.card_eq]
    · intro v hv
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hvT
      · exact hjW
      · intro hvW
        exact T.avoids v hvT (Or.inl hvW)
  · intro S
    apply ContainingIndependentConfiguration.ext
    exact Finset.insert_erase S.contains
  · intro T
    apply AvoidingIndependentConfiguration.ext
    have hjClosed : j ∈ G.closedNeighborhood j := by
      simp [closedNeighborhood]
    have hjNotT : j ∉ T.carrier := by
      intro hjT
      exact T.avoids j hjT (Or.inr hjClosed)
    simp [hjNotT]

end SimpleGraph
