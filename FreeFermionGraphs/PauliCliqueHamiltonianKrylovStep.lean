import FreeFermionGraphs.PauliPathOperatorWeightedCancellation
import FreeFermionGraphs.PauliCliqueHamiltonianExtension

/-!
# Exact one-step Pauli Krylov expansion

This module expands the commutator of the physical Hamiltonian with one
clique-rooted path operator.  The artificial root is excluded, every original
term commuting with the path vanishes, and the remaining finite sum is
supported exactly on original vertices having odd path-neighbour parity.

This is the operator side of Eq. (E11) before the odd external-neighbour terms
are divided into terminal contraction, one-vertex extension, deformation
pairs, and generalized-cycle pairs.
-/

open scoped BigOperators

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Original Hamiltonian vertices whose terms anticommute with the displayed
rooted path operator. -/
noncomputable def anticommutingOriginalVertices
    [Fintype V]
    (P : CliqueRootedInducedPath G K) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun j => P.path.AnticommutesWith (some j))

@[simp]
theorem mem_anticommutingOriginalVertices
    [Fintype V]
    (P : CliqueRootedInducedPath G K) (j : V) :
    j ∈ anticommutingOriginalVertices P ↔
      P.path.AnticommutesWith (some j) := by
  classical
  simp [anticommutingOriginalVertices]

/-- Literal expansion of the physical Hamiltonian commutator into graph
controlled one-term commutators. -/
theorem commutator_physicalHamiltonian_pathOperator_eq_sum
    [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) :
    algebraCommutator H.physicalHamiltonian (H.pathOperator P) =
      ∑ j : V,
        (((-1 : A) ^
            ((P.path.neighborIndexSet (some j)).ncard)) - 1) *
          (H.pathOperator P * H.operator.term (some j)) := by
  rw [H.commutator_physicalHamiltonian_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact H.operator.commutator_term_pathOperator (some j) P.path

/-- Eq. (E11) support reduction: only original vertices anticommuting with the
path remain, and every such term has the common commutator factor
`(-1) - 1`. -/
theorem commutator_physicalHamiltonian_pathOperator_eq_anticommuting_sum
    [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) :
    algebraCommutator H.physicalHamiltonian (H.pathOperator P) =
      ∑ j ∈ anticommutingOriginalVertices P,
        ((-1 : A) - 1) *
          (H.pathOperator P * H.operator.term (some j)) := by
  rw [H.commutator_physicalHamiltonian_eq_sum]
  classical
  rw [anticommutingOriginalVertices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hanti : P.path.AnticommutesWith (some j)
  · simp only [hanti, if_true]
    exact H.operator.commutator_term_pathOperator_of_anticommutesWith
      (some j) P.path hanti
  · have hcomm : P.path.CommutesWith (some j) := by
      rcases P.path.commutesWith_or_anticommutesWith (some j) with h | h
      · exact h
      · exact (hanti h).elim
    simp only [hanti, if_false]
    exact H.operator.commutator_term_pathOperator_eq_zero_of_commutesWith
      (some j) P.path hcomm

/-- Scalar-linear version of the one-step support expansion, ready for a
matrix-row coefficient in the Krylov induction. -/
theorem commutator_physicalHamiltonian_smul_pathOperator_eq_anticommuting_sum
    [Fintype V]
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (a : R) (P : CliqueRootedInducedPath G K) :
    algebraCommutator H.physicalHamiltonian (a • H.pathOperator P) =
      ∑ j ∈ anticommutingOriginalVertices P,
        a • (((-1 : A) - 1) *
          (H.pathOperator P * H.operator.term (some j))) := by
  change commutatorLinearMap (R := R) H.physicalHamiltonian
      (a • H.pathOperator P) = _
  rw [LinearMap.map_smul, commutatorLinearMap_apply]
  rw [H.commutator_physicalHamiltonian_pathOperator_eq_anticommuting_sum]
  rw [Finset.smul_sum]

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
