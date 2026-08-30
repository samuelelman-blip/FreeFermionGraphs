import FreeFermionGraphs.PauliPathOperatorExtension
import FreeFermionGraphs.WeightedHoppingMatrix
import FreeFermionGraphs.Lemma11BBase

/-!
# Pauli Hamiltonians at a clique-rooted induced-path tree

Appendix E works in the root-adjoined graph `G∗`: the artificial root term is
the initial operator `χ`, while the Hamiltonian itself is the sum over only the
original vertices.  This module records that distinction and adds exactly the
Pauli normalization needed for the contraction coefficient `b_j ^ 2`.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace IndexedInducedPath

variable {G : SimpleGraph V}

/-- The terminal vertex of a path with at least two vertices has exactly its
predecessor as a path neighbour, hence anticommutes with the ordered path
operator. -/
theorem terminalVertex_anticommutesWith
    (P : IndexedInducedPath G) (htwo : 2 ≤ P.card) :
    P.AnticommutesWith P.terminalVertex := by
  let last : Fin P.card :=
    ⟨P.card - 1, Nat.sub_lt P.nonempty (by decide)⟩
  let previous : Fin P.card := ⟨P.card - 2, by omega⟩
  change P.AnticommutesWith (P.vertex last)
  apply P.anticommutesWith_of_unique_neighbor
  · apply (P.adj_iff last previous).2
    right
    dsimp [last, previous]
    omega
  · intro q hq
    apply Fin.ext
    rcases (P.adj_iff last q).1 hq with h | h
    · change (P.card - 1) + 1 = q.val at h
      have hq_lt := q.isLt
      omega
    · change q.val + 1 = P.card - 1 at h
      change q.val = P.card - 2
      omega

end IndexedInducedPath

/-- The operator data used in Appendix E on the root-adjoined graph.

The root term is the initial operator `χ`.  Each original term includes its
coupling and squares to the central scalar `b_j ^ 2`, the only extra Pauli
normalization needed for the tree-contraction term in Eq. (E11). -/
structure PauliCliqueHamiltonianRepresentation
    (G : SimpleGraph V) (K : Set V) (R : Type v) (A : Type w)
    [CommRing R] [Ring A] [Algebra R A] where
  operator : (G.adjoinRootAt K).PauliFrustrationRepresentation A
  coupling : V → R
  original_term_sq : ∀ j : V,
    operator.term (some j) * operator.term (some j) =
      algebraMap R A (coupling j ^ 2)

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- The physical Hamiltonian excludes the artificial root term. -/
noncomputable def physicalHamiltonian
    [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) : A :=
  ∑ j : V, H.operator.term (some j)

/-- The artificial root term is the initial operator `χ`. -/
def rootOperator
    (H : G.PauliCliqueHamiltonianRepresentation K R A) : A :=
  H.operator.term none

/-- The manuscript operator `h_P` for a path in the clique-rooted tree.  The
first factor is the artificial-root operator `χ`. -/
def pathOperator
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) : A :=
  H.operator.pathOperator P.path

/-- Expanding the physical Hamiltonian commutator sums only the original
Hamiltonian terms, never the artificial root operator. -/
theorem commutator_physicalHamiltonian_eq_sum
    [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A) (x : A) :
    algebraCommutator H.physicalHamiltonian x =
      ∑ j : V, algebraCommutator (H.operator.term (some j)) x := by
  classical
  simp only [algebraCommutator, physicalHamiltonian, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_sub_distrib]

/-- Exact tree-contraction contribution from Eq. (E11).  If `Q` extends `P`
by the original terminal vertex `j`, commuting the terminal term through
`h_Q` contracts the path and produces the central coefficient `b_j ^ 2`.
-/
theorem terminal_commutator_of_extension
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    {P Q : CliqueRootedInducedPath G K}
    (h : P.IsOneVertexExtension Q) {j : V}
    (hterminal : Q.path.terminalVertex = some j) :
    algebraCommutator (H.operator.term (some j)) (H.pathOperator Q) =
      ((-1 : A) - 1) *
        (algebraMap R A (H.coupling j ^ 2) * H.pathOperator P) := by
  rcases h with ⟨hcard, hprefix⟩
  have htwo : 2 ≤ Q.path.card := by
    have hpos := P.path.nonempty
    omega
  have hanti : Q.path.AnticommutesWith (some j) := by
    simpa only [hterminal] using
      Q.path.terminalVertex_anticommutesWith htwo
  change algebraCommutator (H.operator.term (some j))
      (H.operator.pathOperator Q.path) =
    ((-1 : A) - 1) *
      (algebraMap R A (H.coupling j ^ 2) *
        H.operator.pathOperator P.path)
  rw [H.operator.commutator_term_pathOperator_of_anticommutesWith
    (some j) Q.path hanti]
  rw [H.operator.pathOperator_extension
    (⟨hcard, hprefix⟩ : P.IsOneVertexExtension Q)]
  rw [hterminal]
  simp only [mul_assoc]
  rw [H.original_term_sq]
  rw [← Algebra.commutes]

end PauliCliqueHamiltonianRepresentation
end SimpleGraph
