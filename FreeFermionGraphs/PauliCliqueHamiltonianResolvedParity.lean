import FreeFermionGraphs.PauliCliqueHamiltonianBubbleWandArc

/-!
# Parity-refined one-term Hamiltonian action

The two generalized-cycle alternatives in the resolved action are now split
by the parity of the constructed indexed hole.  Even root hoops carry a
literal alternating labeling, and even bubble-wand hoops carry a concrete
Definition 18 arc.  Odd hoops remain precisely the cancellation cases from
Appendix E.
-/

universe u v w

variable {V : Type u}

namespace SimpleGraph

namespace PauliCliqueHamiltonianRepresentation

variable {G : SimpleGraph V} {K : Set V}
variable {R : Type v} {A : Type w}
variable [CommRing R] [Ring A] [Algebra R A]

/-- The exact one-term action with every generalized-cycle branch refined
into its even contribution or odd cancellation geometry. -/
inductive ResolvedOneTermParityCase
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) (j : V) : Prop
  | contraction
      (Q : CliqueRootedInducedPath G K)
      (extension : Q.IsOneVertexExtension P)
      (commutator :
        algebraCommutator (H.operator.term (some j)) (H.pathOperator P) =
          ((-1 : A) - 1) *
            (algebraMap R A (H.coupling j ^ 2) * H.pathOperator Q)) :
      ResolvedOneTermParityCase H P j
  | extension
      (Q : CliqueRootedInducedPath G K)
      (extension : P.IsOneVertexExtension Q)
      (commutator :
        algebraCommutator (H.operator.term (some j)) (H.pathOperator P) =
          ((-1 : A) - 1) * H.pathOperator Q) :
      ResolvedOneTermParityCase H P j
  | deformation
      (i : Fin P.path.card)
      (data : P.path.SingleVertexDeformation (some j) i)
      (cancellation :
        H.pathOperator P * H.operator.term (some j) +
          H.pathOperator (P.deform data) *
            H.operator.term (P.path.vertex i) = 0) :
      ResolvedOneTermParityCase H P j
  | evenRootHoop
      (C : IndexedInducedHole G)
      (carrier : Set.range C.vertex = P.originalCarrier ∪ {j})
      (k : Nat) (E : EvenHoleLabeling G k)
      (labelCarrier : E.carrier = P.originalCarrier ∪ {j}) :
      ResolvedOneTermParityCase H P j
  | oddRootHoop
      (C : IndexedInducedHole G)
      (carrier : Set.range C.vertex = P.originalCarrier ∪ {j})
      (odd : Odd C.card) :
      ResolvedOneTermParityCase H P j
  | evenBubbleWand
      (B : BubbleWand G)
      (source : P.originalCarrier = Set.range B.path.vertex)
      (bubble : B.bubble = j)
      (ordered : ∃ htail : 2 ≤ P.path.card,
        B.path = P.originalTail htail)
      (Q : CliqueRootedInducedPath G K)
      (arc : EvenHoopBubbleWandArc G K P Q) :
      ResolvedOneTermParityCase H P j
  | oddBubbleWand
      (B : BubbleWand G)
      (source : P.originalCarrier = Set.range B.path.vertex)
      (bubble : B.bubble = j)
      (ordered : ∃ htail : 2 ≤ P.path.card,
        B.path = P.originalTail htail)
      (odd : Odd B.hoopHole.card) :
      ResolvedOneTermParityCase H P j

/-- Refine an already resolved one-term action by the literal parity of its
constructed root hoop or bubble-wand hoop. -/
theorem ResolvedOneTermActionCase.refineParity
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K) {j : V}
    (h : ResolvedOneTermActionCase H P j) :
    ResolvedOneTermParityCase H P j := by
  rcases h with
    ⟨Q, hQP, hcommutator⟩ |
    ⟨Q, hPQ, hcommutator⟩ |
    ⟨i, hdata, hcancellation⟩ |
    ⟨C, hcarrier⟩ |
    ⟨B, hsource, hbubble, hordered⟩
  · exact .contraction Q hQP hcommutator
  · exact .extension Q hPQ hcommutator
  · exact .deformation i hdata hcancellation
  · rcases Nat.even_or_odd C.card with hEven | hOdd
    · obtain ⟨k, E, hlabel⟩ := C.exists_evenHoleLabeling hEven
      exact .evenRootHoop C hcarrier k E (hlabel.trans hcarrier)
    · exact .oddRootHoop C hcarrier hOdd
  · rcases Nat.even_or_odd B.hoopHole.card with hEven | hOdd
    · obtain ⟨Q, hArc⟩ :=
        exists_evenHoopBubbleWandArc P B hsource hordered hEven
      exact .evenBubbleWand B hsource hbubble hordered Q hArc
    · exact .oddBubbleWand B hsource hbubble hordered hOdd

/-- Complete parity-refined classification of every exact anticommuting
Hamiltonian term. -/
theorem resolvedOneTermParityCase
    (H : G.PauliCliqueHamiltonianRepresentation K R A)
    (P : CliqueRootedInducedPath G K)
    (hK : G.IsSimplicialClique K) (hclaw : G.IsClawFree)
    {j : V} (hanti : P.path.AnticommutesWith (some j)) :
    ResolvedOneTermParityCase H P j :=
  (H.resolvedOneTermActionCase P hK hclaw hanti).refineParity H P

end PauliCliqueHamiltonianRepresentation

end SimpleGraph
