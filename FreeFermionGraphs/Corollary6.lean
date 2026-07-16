import FreeFermionGraphs.Lemma9

/-!
# Compatibility of deformation closures

This file formalizes Corollary 6: compatibility with an even hole is
preserved throughout its deformation closure.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

/-- Two even-hole carriers are compatible when their open neighborhoods are
disjoint.  For hole carriers this is the paper's condition that their induced
union has the two holes as separate connected components. -/
def EvenHoleCompatible (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint (G.openNeighborhood A) (G.openNeighborhood B)

/-- Compatibility is symmetric. -/
theorem evenHoleCompatible_comm {A B : Set V} :
    G.EvenHoleCompatible A B ↔ G.EvenHoleCompatible B A := by
  exact disjoint_comm

/-- Compatibility with the second carrier is invariant under deformation. -/
theorem InEvenHoleDeformationClosure.evenHoleCompatible_right_iff
    {A B C : Set V} (hclosure : InEvenHoleDeformationClosure G A B)
    (hclaw : G.IsClawFree) :
    G.EvenHoleCompatible C A ↔ G.EvenHoleCompatible C B := by
  unfold EvenHoleCompatible
  rw [hclosure.openNeighborhood_eq hclaw]

/-- Corollary 6 of the paper: if an even hole is compatible with one carrier,
it is compatible with every carrier in that carrier's deformation closure. -/
theorem corollary6 {A B C : Set V}
    (hclosure : InEvenHoleDeformationClosure G A B)
    (hclaw : G.IsClawFree)
    (hcompat : G.EvenHoleCompatible C A) :
    G.EvenHoleCompatible C B := by
  exact (hclosure.evenHoleCompatible_right_iff hclaw).mp hcompat

end SimpleGraph
