import FreeFermionGraphs.Lemma11BConsecutiveFourCommonNeighbor
import FreeFermionGraphs.EvenHoleLabeling

/-!
# Lemma 11(b): alternating coordinates for consecutive removals

The deformation sequence stores each hole only as an indexed cyclic carrier.
The paper additionally uses the alternating coordinates

`b₀-a₀-b₁-a₁-⋯-bₖ₋₁-aₖ₋₁-b₀`.

For consecutive steps, if the current removed vertex is `a r`, the next
removed vertex is `a (next r)`.  Their common neighbor on the earlier hole
is therefore the explicit vertex `b (next r)`.  This module records exactly
that coordinate datum and derives the abstract common-neighbor rule used by
the deformation bridge.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Alternating coordinates on every before-hole in a one-path deformation.

The final field is the paper's order information: at consecutive deformation
steps, the next removed vertex is the next `a`-vertex in the earlier
alternating labeling. -/
structure AlternatingHoleCoordinates
    (D : ConcretePathDeformation O Cprime) where
  halfLength : Fin D.deformation.stepCount → Nat
  labeling :
    ∀ i : Fin D.deformation.stepCount,
      EvenHoleLabeling G (halfLength i)
  removedAIndex :
    ∀ i : Fin D.deformation.stepCount, Fin (halfLength i)
  carrier_eq :
    ∀ i : Fin D.deformation.stepCount,
      (labeling i).carrier =
        Set.range (D.deformation.step i).before.vertex
  removed_eq :
    ∀ i : Fin D.deformation.stepCount,
      (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex =
        (labeling i).a (removedAIndex i)
  next_removed_eq :
    ∀ ⦃i j : Fin D.deformation.stepCount⦄,
      i.val + 1 = j.val →
      (D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex =
        (labeling i).a ((labeling i).next (removedAIndex i))

namespace AlternatingHoleCoordinates

variable {D : ConcretePathDeformation O Cprime}

/-- The alternating coordinates discharge the raw common-neighbor rule:
`b (next r)` neighbors both `a r` and `a (next r)`. -/
theorem consecutiveRemovedCommonNeighborRule
    (H : D.AlternatingHoleCoordinates) :
    D.ConsecutiveRemovedCommonNeighborRule := by
  intro i j hij
  refine
    ⟨(H.labeling i).b
        ((H.labeling i).next (H.removedAIndex i)), ?_, ?_, ?_⟩
  · rw [← H.carrier_eq i]
    exact (H.labeling i).b_mem_carrier
      ((H.labeling i).next (H.removedAIndex i))
  · rw [H.removed_eq i]
    exact (H.labeling i).adj_a_b_next (H.removedAIndex i)
  · rw [H.next_removed_eq hij]
    exact (H.labeling i).adj_a_b
      ((H.labeling i).next (H.removedAIndex i))

/-- Paper-faithful alternating coordinates supply the complete
`w_(s-1)` certificate for every consecutive pair of deformation steps. -/
theorem consecutiveFourCommonNeighborRule
    (H : D.AlternatingHoleCoordinates)
    (M : D.MechanicalData) :
    ∀ ⦃i j : Fin D.deformation.stepCount⦄,
      i.val + 1 = j.val →
      D.HasConsecutiveFourCommonNeighbor i j :=
  D.consecutiveFourCommonNeighborRule_of_removedCommonNeighbors
    M H.consecutiveRemovedCommonNeighborRule

end AlternatingHoleCoordinates

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
