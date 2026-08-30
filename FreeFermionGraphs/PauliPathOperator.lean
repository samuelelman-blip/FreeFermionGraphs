import FreeFermionGraphs.PauliFrustrationRepresentation
import FreeFermionGraphs.KrylovMatrixRealization
import FreeFermionGraphs.InducedStructures
import FreeFermionGraphs.Lemma11PathCounts
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Ring.Parity

/-!
# Pauli operators attached to induced paths

The operator basis in manuscript Theorem 3 consists of ordered products of
Hamiltonian terms along induced paths.  This file constructs those products
directly from a `PauliFrustrationRepresentation` and proves the basic sign
transport which makes the graph control their commutators.

Moving one Pauli term through a path product contributes one minus sign for
each frustration edge from that term to the path.  Thus the total sign is
determined by the path-neighbour count, exactly the quantity classified by
Lemma 7.
-/

open scoped BigOperators

universe u w

variable {V : Type u}

namespace SimpleGraph
namespace PauliFrustrationRepresentation

variable {G : SimpleGraph V} {A : Type w} [Ring A]

/-- The Hamiltonian is the finite sum of its Pauli terms. -/
noncomputable def hamiltonian
    [Fintype V]
    (H : G.PauliFrustrationRepresentation A) : A :=
  ∑ j : V, H.term j

/-- Ordered product of term operators along an arbitrary vertex list. -/
def listOperator
    (H : G.PauliFrustrationRepresentation A) (vertices : List V) : A :=
  (vertices.map H.term).prod

/-- Number of listed vertices adjacent to `j`.  The definition is
noncomputable so public sign theorems do not carry a choice of decidable
adjacency as mathematical data. -/
noncomputable def listNeighborCount
    (G : SimpleGraph V) (j : V) (vertices : List V) : Nat := by
  classical
  exact vertices.countP fun v => decide (G.Adj j v)

@[simp]
theorem listNeighborCount_nil (G : SimpleGraph V) (j : V) :
    listNeighborCount G j [] = 0 := by
  classical
  simp [listNeighborCount]

theorem listNeighborCount_cons_of_adj
    (G : SimpleGraph V) {j v : V} (vertices : List V)
    (h : G.Adj j v) :
    listNeighborCount G j (v :: vertices) =
      listNeighborCount G j vertices + 1 := by
  classical
  simp [listNeighborCount, h]

theorem listNeighborCount_cons_of_not_adj
    (G : SimpleGraph V) {j v : V} (vertices : List V)
    (h : ¬G.Adj j v) :
    listNeighborCount G j (v :: vertices) =
      listNeighborCount G j vertices := by
  classical
  simp [listNeighborCount, h]

@[simp]
theorem listOperator_nil
    (H : G.PauliFrustrationRepresentation A) :
    H.listOperator [] = 1 :=
  rfl

@[simp]
theorem listOperator_cons
    (H : G.PauliFrustrationRepresentation A) (j : V) (vertices : List V) :
    H.listOperator (j :: vertices) =
      H.term j * H.listOperator vertices :=
  rfl

/-- The manuscript path operator `h_P`, with multiplication in the displayed
linear order of the indexed induced path. -/
def pathOperator
    (H : G.PauliFrustrationRepresentation A)
    (P : IndexedInducedPath G) : A :=
  H.listOperator (List.ofFn P.vertex)

/-- Expanding the Hamiltonian commutator is the sum of the individual term
commutators. -/
theorem commutator_hamiltonian_eq_sum
    [Fintype V]
    (H : G.PauliFrustrationRepresentation A) (x : A) :
    algebraCommutator H.hamiltonian x =
      ∑ j : V, algebraCommutator (H.term j) x := by
  classical
  simp only [algebraCommutator, hamiltonian, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_sub_distrib]

/-- Crossing a term through an ordered operator list produces one minus sign
for every frustration edge from that term to a listed vertex. -/
theorem term_mul_listOperator
    (H : G.PauliFrustrationRepresentation A)
    (j : V) (vertices : List V) :
    H.term j * H.listOperator vertices =
      (-1 : A) ^ (listNeighborCount G j vertices) *
        (H.listOperator vertices * H.term j) := by
  classical
  induction vertices with
  | nil => simp
  | cons v vertices ih =>
      by_cases hjv : G.Adj j v
      · calc
          H.term j * H.listOperator (v :: vertices) =
              (H.term j * H.term v) * H.listOperator vertices := by
                simp only [listOperator_cons, mul_assoc]
          _ = -(H.term v * H.term j) * H.listOperator vertices := by
                rw [H.adj_iff_anticommute.mp hjv]
          _ = -(H.term v * (H.term j * H.listOperator vertices)) := by
                simp only [mul_assoc, neg_mul]
          _ = -(H.term v *
                (((-1 : A) ^ (listNeighborCount G j vertices)) *
                  (H.listOperator vertices * H.term j))) := by
                rw [ih]
          _ = (-1 : A) ^ (listNeighborCount G j (v :: vertices)) *
                (H.listOperator (v :: vertices) * H.term j) := by
                rw [listNeighborCount_cons_of_adj G vertices hjv, pow_succ]
                have hs := (Commute.neg_one_left (H.term v)).pow_left
                  (listNeighborCount G j vertices)
                rw [← hs.left_comm]
                simp only [listOperator_cons, mul_assoc, neg_mul, mul_neg,
                  one_mul]
      · calc
          H.term j * H.listOperator (v :: vertices) =
              (H.term j * H.term v) * H.listOperator vertices := by
                simp only [listOperator_cons, mul_assoc]
          _ = (H.term v * H.term j) * H.listOperator vertices := by
                rw [H.commute_of_not_adj hjv]
          _ = H.term v * (H.term j * H.listOperator vertices) := by
                simp only [mul_assoc]
          _ = H.term v *
                (((-1 : A) ^ (listNeighborCount G j vertices)) *
                  (H.listOperator vertices * H.term j)) := by
                rw [ih]
          _ = (-1 : A) ^ (listNeighborCount G j (v :: vertices)) *
                (H.listOperator (v :: vertices) * H.term j) := by
                rw [listNeighborCount_cons_of_not_adj G vertices hjv]
                have hs := (Commute.neg_one_left (H.term v)).pow_left
                  (listNeighborCount G j vertices)
                rw [← hs.left_comm]
                simp only [listOperator_cons, mul_assoc]

/-- Exact one-term commutator formula.  The coefficient is zero for an even
neighbour count and `-2` for an odd neighbour count. -/
theorem commutator_term_listOperator
    (H : G.PauliFrustrationRepresentation A)
    (j : V) (vertices : List V) :
    algebraCommutator (H.term j) (H.listOperator vertices) =
      (((-1 : A) ^ (listNeighborCount G j vertices)) - 1) *
        (H.listOperator vertices * H.term j) := by
  rw [algebraCommutator, H.term_mul_listOperator, sub_mul, one_mul]

/-- A term with an even number of frustration edges to the list commutes with
its ordered operator product. -/
theorem commutator_term_listOperator_eq_zero_of_even
    (H : G.PauliFrustrationRepresentation A)
    (j : V) (vertices : List V)
    (heven : Even (listNeighborCount G j vertices)) :
    algebraCommutator (H.term j) (H.listOperator vertices) = 0 := by
  rw [H.commutator_term_listOperator, heven.neg_one_pow]
  simp

/-- A term with an odd number of frustration edges contributes `-2` times
right multiplication by that term. -/
theorem commutator_term_listOperator_of_odd
    (H : G.PauliFrustrationRepresentation A)
    (j : V) (vertices : List V)
    (hodd : Odd (listNeighborCount G j vertices)) :
    algebraCommutator (H.term j) (H.listOperator vertices) =
      ((-1 : A) - 1) * (H.listOperator vertices * H.term j) := by
  rw [H.commutator_term_listOperator, hodd.neg_one_pow]

/-- For an indexed path, the list count is the cardinality of the path's
indexed neighbour set. -/
theorem listNeighborCount_path_eq_neighborIndexSet_ncard
    (P : IndexedInducedPath G) (j : V) :
    listNeighborCount G j (List.ofFn P.vertex) =
      (P.neighborIndexSet j).ncard := by
  classical
  have hnodup :
      ((List.ofFn P.vertex).filter fun v => decide (G.Adj j v)).Nodup :=
    (List.nodup_ofFn.mpr P.injective).filter _
  have hfinite : (G.adjacentIn j (Set.range P.vertex)).Finite :=
    (Set.finite_range P.vertex).subset fun _ hv => hv.1
  calc
    listNeighborCount G j (List.ofFn P.vertex) =
        ((List.ofFn P.vertex).filter fun v => decide (G.Adj j v)).length := by
          simp [listNeighborCount, List.countP_eq_length_filter]
    _ = ((List.ofFn P.vertex).filter
          fun v => decide (G.Adj j v)).toFinset.card :=
        (List.toFinset_card_of_nodup hnodup).symm
    _ = (G.adjacentIn j (Set.range P.vertex)).ncard := by
      rw [Set.ncard_eq_toFinset_card _ hfinite]
      congr 1
      ext v
      simp [SimpleGraph.adjacentIn]
    _ = (P.neighborIndexSet j).ncard :=
      P.adjacencyCount_range_eq_neighborIndexSet_ncard j

/-- The crossing-sign theorem specialized to an indexed induced path. -/
theorem term_mul_pathOperator
    (H : G.PauliFrustrationRepresentation A)
    (j : V) (P : IndexedInducedPath G) :
    H.term j * H.pathOperator P =
      (-1 : A) ^ ((P.neighborIndexSet j).ncard) *
        (H.pathOperator P * H.term j) :=
  by
    rw [← listNeighborCount_path_eq_neighborIndexSet_ncard P j]
    exact H.term_mul_listOperator j (List.ofFn P.vertex)

/-- Exact commutator of one Hamiltonian term with a path operator, expressed
by the graph-theoretic neighbour count. -/
theorem commutator_term_pathOperator
    (H : G.PauliFrustrationRepresentation A)
    (j : V) (P : IndexedInducedPath G) :
    algebraCommutator (H.term j) (H.pathOperator P) =
      (((-1 : A) ^ ((P.neighborIndexSet j).ncard)) - 1) *
        (H.pathOperator P * H.term j) := by
  rw [algebraCommutator, H.term_mul_pathOperator, sub_mul, one_mul]

/-- Graph-level path commutation implies the operator commutator vanishes. -/
theorem commutator_term_pathOperator_eq_zero_of_commutesWith
    (H : G.PauliFrustrationRepresentation A)
    (j : V) (P : IndexedInducedPath G)
    (hcomm : P.CommutesWith j) :
    algebraCommutator (H.term j) (H.pathOperator P) = 0 := by
  have hmod : (P.neighborIndexSet j).ncard % 2 = 0 :=
    (P.commutesWith_iff_neighborIndexSet_mod_eq_zero j).mp hcomm
  have heven : Even (P.neighborIndexSet j).ncard :=
    Nat.not_odd_iff_even.mp ((Nat.not_odd_iff).mpr hmod)
  rw [H.commutator_term_pathOperator, heven.neg_one_pow]
  simp

/-- Graph-level path anticommutation gives the `-2` one-term contribution
used in the manuscript's one-step Krylov expansion. -/
theorem commutator_term_pathOperator_of_anticommutesWith
    (H : G.PauliFrustrationRepresentation A)
    (j : V) (P : IndexedInducedPath G)
    (hanti : P.AnticommutesWith j) :
    algebraCommutator (H.term j) (H.pathOperator P) =
      ((-1 : A) - 1) * (H.pathOperator P * H.term j) := by
  have hodd : Odd (P.neighborIndexSet j).ncard :=
    Nat.odd_iff.mpr
      ((P.anticommutesWith_iff_neighborIndexSet_mod_eq_one j).mp hanti)
  rw [H.commutator_term_pathOperator, hodd.neg_one_pow]

end PauliFrustrationRepresentation
end SimpleGraph
