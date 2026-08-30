import FreeFermionGraphs.PauliCliqueHamiltonianTerminalContraction
import FreeFermionGraphs.PauliCliqueHamiltonianEndpointExtension
import FreeFermionGraphs.PauliPathOperatorCancellation

/-!
# Resolved one-term Hamiltonian action

Every anticommuting term in the physical Hamiltonian now has an operator-facing
case.  Tree endpoints produce exact forward or backward Eq. (E11) terms,
literal deformations carry the raw Eq. (E12) cancellation identity, and the
two exceptional cases carry constructed root-hoop or bubble-wand geometry.
-/

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- Operator-facing alternatives for one original vertex in the exact
anticommuting support of a clique-rooted path. -/
inductive ResolvedOneTermActionCase
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) (j : V) : Prop
  | contraction
      (Q : CliqueRootedInducedPath G K)
      (extension : Q.IsOneVertexExtension P)
      (commutator :
        algebraCommutator (H.operator.term (some j)) (H.pathOperator P) =
          ((-1 : A) - 1) *
            (algebraMap R A (H.coupling j ^ 2) * H.pathOperator Q)) :
      ResolvedOneTermActionCase H P j
  | extension
      (Q : CliqueRootedInducedPath G K)
      (extension : P.IsOneVertexExtension Q)
      (commutator :
        algebraCommutator (H.operator.term (some j)) (H.pathOperator P) =
          ((-1 : A) - 1) * H.pathOperator Q) :
      ResolvedOneTermActionCase H P j
  | deformation
      (i : Fin P.path.card)
      (data : P.path.SingleVertexDeformation (some j) i)
      (cancellation :
        H.pathOperator P * H.operator.term (some j) +
          H.pathOperator (P.deform data) *
            H.operator.term (P.path.vertex i) = 0) :
      ResolvedOneTermActionCase H P j
  | rootHoop
      (C : IndexedInducedHole G)
      (carrier : Set.range C.vertex = P.originalCarrier ∪ {j}) :
      ResolvedOneTermActionCase H P j
  | bubbleWand
      (B : BubbleWand G)
      (source : P.originalCarrier = Set.range B.path.vertex)
      (bubble : B.bubble = j)
      (ordered : ∃ htail : 2 ≤ P.path.card,
        B.path = P.originalTail htail) :
      ResolvedOneTermActionCase H P j

/-- Complete one-term refinement of the exact anticommuting support. -/
theorem resolvedOneTermActionCase
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {j : V} (hanti : P.path.AnticommutesWith (some j)) :
    ResolvedOneTermActionCase H P j := by
  rcases P.resolvedOriginalAnticommutingCase hK hclaw hanti with
    hterminal | ⟨houtside, hgeometry⟩
  · obtain ⟨Q, hQP, hcommutator⟩ := H.terminal_commutator P hterminal
    exact .contraction Q hQP hcommutator
  · rcases hgeometry with
      ⟨q, hjq, hqEndpoint, hexact⟩ |
      ⟨i, hdeformation⟩ |
      ⟨C, hcarrier⟩ |
      ⟨B, hsource, hbubble, hordered⟩
    · obtain ⟨Q, hPQ, hcommutator⟩ :=
        H.exists_extension_commutator_of_uniqueOriginalEndpoint
          P hK.isClique houtside hjq hqEndpoint hexact
      exact .extension Q hPQ hcommutator
    · apply ResolvedOneTermActionCase.deformation i hdeformation
      exact H.operator.pathOperator_deformation_add_eq_zero
        P.path hdeformation
    · exact .rootHoop C hcarrier
    · exact .bubbleWand B hsource hbubble hordered

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
