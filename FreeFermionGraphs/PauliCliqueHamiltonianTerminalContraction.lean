import FreeFermionGraphs.PauliCliqueHamiltonianResolvedSupport
import FreeFermionGraphs.InducedPathDeformationPrefixes

/-!
# Canonical terminal contraction for a clique-rooted path

The terminal alternative in the resolved Hamiltonian support has a canonical
predecessor: remove the last indexed vertex.  This module constructs that
prefix and applies the exact contraction identity from Eq. (E11), so callers
do not have to supply a shorter path as extra data.
-/

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace RootedInducedPath

variable {G : SimpleGraph V} {K : Set V}

/-- A clique-rooted path whose terminal vertex is original has at least the
artificial root and that terminal vertex. -/
theorem card_two_of_terminalVertex_eq_some
    (P : CliqueRootedInducedPath G K) {j : V}
    (hterminal : P.path.terminalVertex = some j) :
    2 ≤ P.path.card := by
  by_contra hcard
  have hpositive : 0 < P.path.card := P.path.nonempty
  have hcardOne : P.path.card = 1 := by omega
  have hlastZero :
      (⟨P.path.card - 1,
          Nat.sub_lt P.path.nonempty (by decide)⟩ : Fin P.path.card) =
        ⟨0, P.path.nonempty⟩ := by
    apply Fin.ext
    omega
  unfold IndexedInducedPath.terminalVertex at hterminal
  rw [hlastZero, P.root_eq] at hterminal
  simp at hterminal

/-- Removing the original terminal vertex gives a canonical predecessor in
the clique-rooted induced-path tree. -/
theorem exists_terminalPredecessor
    (P : CliqueRootedInducedPath G K) {j : V}
    (hterminal : P.path.terminalVertex = some j) :
    ∃ Q : CliqueRootedInducedPath G K, Q.IsOneVertexExtension P := by
  have htwo := P.card_two_of_terminalVertex_eq_some hterminal
  let previous : Fin P.path.card :=
    ⟨P.path.card - 2, by omega⟩
  let Q : CliqueRootedInducedPath G K := P.initialSegment previous
  refine ⟨Q, ?_⟩
  refine ⟨?_, ?_⟩
  · change (P.path.card - 2 + 1) + 1 = P.path.card
    omega
  · intro q
    rfl

end RootedInducedPath

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- The terminal support case produces the canonical backward tree term of
Eq. (E11), with its predecessor constructed from the given path. -/
theorem terminal_commutator
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) {j : V}
    (hterminal : P.path.terminalVertex = some j) :
    ∃ Q : CliqueRootedInducedPath G K,
      Q.IsOneVertexExtension P ∧
      algebraCommutator (H.operator.term (some j)) (H.pathOperator P) =
        ((-1 : A) - 1) *
          (algebraMap R A (H.coupling j ^ 2) * H.pathOperator Q) := by
  obtain ⟨Q, hQP⟩ := P.exists_terminalPredecessor hterminal
  exact ⟨Q, hQP, H.terminal_commutator_of_extension hQP hterminal⟩

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
