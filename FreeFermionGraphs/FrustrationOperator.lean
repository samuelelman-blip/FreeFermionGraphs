import FreeFermionGraphs.SimplicialClique
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Operator-valued independent-set charges

This module introduces the noncommutative operator layer needed for manuscript
Lemma 17.  The earlier `TokenSlidingCharges.independentSetCharge` is a generic
additive combinatorial sum and deliberately does not encode products of
Hamiltonian terms.

The structure below separates two ingredients of the manuscript Hamiltonian
representation:

* one operator `h_j` for every frustration-graph vertex;
* the product `h_S` attached to a finite independent set, together with its
  order-independence at an inserted vertex.

For actual Pauli Hamiltonian terms the two insertion laws follow because all
vertices of an independent set commute pairwise.  Keeping them explicit here
lets the Lemma 17 combinatorics be developed without silently replacing a
noncommutative operator product by a commutative one.  An unqualified
paper-facing theorem will only be exported after this interface is connected
to the concrete Hamiltonian/frustration-graph representation.
-/

open Set
open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- Operator representation of a Hamiltonian whose frustration graph is `G`.

`independentProduct S` is the manuscript operator `h_S`.  The left and right
insertion laws record the order-independence of this product when the inserted
vertex commutes with every vertex already in `S`.

The finite-set insertion operation is computational, so the model carries the
same `DecidableEq V` assumption used by the finite charge sums below. -/
structure FrustrationOperatorModel
    (G : SimpleGraph V) (A : Type w) [Ring A] [DecidableEq V] where
  term : V → A
  independentProduct : Finset V → A
  independentProduct_empty : independentProduct ∅ = 1
  independentProduct_insert_left :
    ∀ {j : V} {S : Finset V},
      j ∉ S →
      G.IsIndepSet (S : Set V) →
      (∀ v ∈ S, ¬G.Adj j v) →
      independentProduct (insert j S) =
        term j * independentProduct S
  independentProduct_insert_right :
    ∀ {j : V} {S : Finset V},
      j ∉ S →
      G.IsIndepSet (S : Set V) →
      (∀ v ∈ S, ¬G.Adj j v) →
      independentProduct (insert j S) =
        independentProduct S * term j
  anticommute_of_adj :
    ∀ {j k : V}, G.Adj j k →
      term j * term k = -(term k * term j)
  commute_of_not_adj :
    ∀ {j k : V}, ¬G.Adj j k →
      term j * term k = term k * term j

namespace FrustrationOperatorModel

variable {G : SimpleGraph V} {A : Type w} [Ring A] [DecidableEq V]

/-- The term operators anticommute on every frustration edge. -/
theorem anticommute
    (M : G.FrustrationOperatorModel A)
    {j k : V} (hjk : G.Adj j k) :
    M.term j * M.term k = -(M.term k * M.term j) :=
  M.anticommute_of_adj hjk

/-- The term operators commute on every nonedge of the frustration graph. -/
theorem commute
    (M : G.FrustrationOperatorModel A)
    {j k : V} (hjk : ¬G.Adj j k) :
    M.term j * M.term k = M.term k * M.term j :=
  M.commute_of_not_adj hjk

end FrustrationOperatorModel

/-- Finite `k`-vertex independent sets that avoid a deleted carrier `W`.

This represents the independent sets of the vertex-deleted graph `G \ W`
without changing the ambient vertex type. -/
noncomputable def independentFinsetsOfCardAvoid
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (W : Set V) (k : Nat) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun S =>
    S.card = k ∧
      G.IsIndepSet (S : Set V) ∧
      ∀ v ∈ S, v ∉ W

@[simp]
theorem mem_independentFinsetsOfCardAvoid
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {W : Set V} {k : Nat} {S : Finset V} :
    S ∈ G.independentFinsetsOfCardAvoid W k ↔
      S.card = k ∧
        G.IsIndepSet (S : Set V) ∧
        ∀ v ∈ S, v ∉ W := by
  classical
  simp [independentFinsetsOfCardAvoid]

/-- Definition 4, Eq. (49), at the operator interface, with an additional
vertex-deletion parameter.

`operatorIndependentSetCharge M W k` is the manuscript
`Q_(G\W)^(k)`.  In particular `W = ∅` gives `Q_G^(k)`. -/
noncomputable def operatorIndependentSetCharge
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    (W : Set V) (k : Nat) : A := by
  classical
  exact ∑ S ∈ G.independentFinsetsOfCardAvoid W k,
    M.independentProduct S

/-- Manuscript notation `Q_G^(k)`. -/
noncomputable def operatorIndependentSetChargeFull
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    {A : Type w} [Ring A]
    (M : G.FrustrationOperatorModel A)
    (k : Nat) : A :=
  G.operatorIndependentSetCharge M ∅ k

/-- Avoiding a larger deleted carrier can only remove summands.  This is a
set-level helper used in the clique recursion proof. -/
theorem independentFinsetsOfCardAvoid_mono
    {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    {W W' : Set V} {k : Nat}
    (hWW' : W ⊆ W') :
    G.independentFinsetsOfCardAvoid W' k ⊆
      G.independentFinsetsOfCardAvoid W k := by
  intro S hS
  rw [mem_independentFinsetsOfCardAvoid] at hS ⊢
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro v hvS hvW
  exact hS.2.2 v hvS (hWW' hvW)

end SimpleGraph
