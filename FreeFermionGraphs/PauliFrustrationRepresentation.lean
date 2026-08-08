import FreeFermionGraphs.Lemma17Recursion
import Mathlib.Data.Finset.NoncommProd

/-!
# Pauli Hamiltonian / frustration-graph representation

The paper-facing boundary for Lemma 17 should not accept an independently
supplied product-coherence certificate.  For Pauli Hamiltonian terms, distinct
nonadjacent frustration-graph vertices commute.  Consequently the product over
an independent set is canonically available as `Finset.noncommProd`, and its
left/right insertion laws are theorems rather than input data.

This module packages only the term operators and the pairwise
commutation/anticommutation relation encoded by the frustration graph, then
derives the `FrustrationOperatorModel` used by the internal Lemma 17 proof.
-/

open Set

universe u w
variable {V : Type u}

namespace SimpleGraph

/-- Minimal algebraic representation of the Pauli Hamiltonian terms together
with their frustration graph.

The first relation is manuscript Definition 1.  The second records the Pauli
commute/anticommute dichotomy on nonedges.  No independent-set product or
insertion law is supplied as data. -/
structure PauliFrustrationRepresentation
    (G : SimpleGraph V) (A : Type w) [Ring A] where
  term : V → A
  adj_iff_anticommute :
    ∀ {j k : V},
      G.Adj j k ↔
        term j * term k = -(term k * term j)
  commute_of_not_adj :
    ∀ {j k : V}, ¬G.Adj j k →
      term j * term k = term k * term j

namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-- Terms indexed by an independent set commute pairwise. -/
theorem independent_pairwise_commute
    (H : G.PauliFrustrationRepresentation A)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    (↑S : Set V).Pairwise (Function.onFun Commute H.term) := by
  intro j hj k hk hjk
  show H.term j * H.term k = H.term k * H.term j
  exact H.commute_of_not_adj (hS hj hk hjk)

/-- Canonical manuscript product `h_S`.

On an independent set this is the well-defined noncommutative finite product
of the mutually commuting Pauli terms.  Its value outside the independent-set
case is irrelevant to the charges and is set to `1`. -/
noncomputable def independentProduct
    (H : G.PauliFrustrationRepresentation A)
    (S : Finset V) : A := by
  classical
  by_cases hS : G.IsIndepSet (S : Set V)
  · exact S.noncommProd H.term (H.independent_pairwise_commute hS)
  · exact 1

/-- On an independent set the canonical product is literally
`Finset.noncommProd`. -/
theorem independentProduct_eq_noncommProd
    (H : G.PauliFrustrationRepresentation A)
    {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    H.independentProduct S =
      S.noncommProd H.term (H.independent_pairwise_commute hS) := by
  classical
  simp [independentProduct, hS]

/-- The canonical independent product of the empty set is the identity. -/
theorem independentProduct_empty
    (H : G.PauliFrustrationRepresentation A) :
    H.independentProduct (∅ : Finset V) = 1 := by
  classical
  have hEmpty : G.IsIndepSet (((∅ : Finset V) : Set V)) := by
    simp
  rw [H.independentProduct_eq_noncommProd hEmpty]
  simp

/-- Inserting a vertex that is nonadjacent to every member of an independent
set multiplies the canonical product on the left. -/
theorem independentProduct_insert_left
    [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    {j : V} {S : Finset V}
    (hjS : j ∉ S)
    (hS : G.IsIndepSet (S : Set V))
    (hNonadj : ∀ v ∈ S, ¬G.Adj j v) :
    H.independentProduct (insert j S) =
      H.term j * H.independentProduct S := by
  classical
  have hAvoid : ∀ v ∈ S, v ∉ G.closedNeighborhood j := by
    intro v hvS hvClosed
    rcases hvClosed with hvj | hvNeighbor
    · have hvEq : v = j := hvj
      subst v
      exact hjS hvS
    · exact hNonadj v hvS ((G.mem_neighborSet j v).mp hvNeighbor)
  have hInsert :
      G.IsIndepSet (((insert j S : Finset V) : Set V)) :=
    isIndepSet_insert_of_avoids_closedNeighborhood hS hAvoid
  rw [H.independentProduct_eq_noncommProd hInsert,
    H.independentProduct_eq_noncommProd hS]
  exact Finset.noncommProd_insert_of_notMem
    S j H.term (H.independent_pairwise_commute hInsert) hjS

/-- The same insertion can be placed on the right because every factor in the
independent set commutes with the inserted term. -/
theorem independentProduct_insert_right
    [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A)
    {j : V} {S : Finset V}
    (hjS : j ∉ S)
    (hS : G.IsIndepSet (S : Set V))
    (hNonadj : ∀ v ∈ S, ¬G.Adj j v) :
    H.independentProduct (insert j S) =
      H.independentProduct S * H.term j := by
  classical
  have hAvoid : ∀ v ∈ S, v ∉ G.closedNeighborhood j := by
    intro v hvS hvClosed
    rcases hvClosed with hvj | hvNeighbor
    · have hvEq : v = j := hvj
      subst v
      exact hjS hvS
    · exact hNonadj v hvS ((G.mem_neighborSet j v).mp hvNeighbor)
  have hInsert :
      G.IsIndepSet (((insert j S : Finset V) : Set V)) :=
    isIndepSet_insert_of_avoids_closedNeighborhood hS hAvoid
  rw [H.independentProduct_eq_noncommProd hInsert,
    H.independentProduct_eq_noncommProd hS]
  exact Finset.noncommProd_insert_of_notMem'
    S j H.term (H.independent_pairwise_commute hInsert) hjS

/-- The internal operator model used in the Lemma 17 derivation is constructed
from the Pauli Hamiltonian/frustration-graph data.  In particular its product
coherence laws are derived, not supplied at the paper-facing boundary. -/
noncomputable def toOperatorModel
    [DecidableEq V]
    (H : G.PauliFrustrationRepresentation A) :
    G.FrustrationOperatorModel A where
  term := H.term
  independentProduct := H.independentProduct
  independentProduct_empty := H.independentProduct_empty
  independentProduct_insert_left := by
    intro j S hjS hS hNonadj
    exact H.independentProduct_insert_left hjS hS hNonadj
  independentProduct_insert_right := by
    intro j S hjS hS hNonadj
    exact H.independentProduct_insert_right hjS hS hNonadj
  anticommute_of_adj := by
    intro j k hjk
    exact H.adj_iff_anticommute.mp hjk
  commute_of_not_adj := by
    intro j k hjk
    exact H.commute_of_not_adj hjk

end PauliFrustrationRepresentation

end SimpleGraph
