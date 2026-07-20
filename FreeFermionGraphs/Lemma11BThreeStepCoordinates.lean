import FreeFermionGraphs.Lemma11BOutsideOrdinaryCommonB

/-!
# Lemma 11(b): coordinates across three consecutive steps

The two-step ordinary predecessor argument compares the hole before the
steps (s-2), (s-1), and (s).  This module records the relevant
identities in the labeling before step (s-2): the next removed coordinate,
the unchanged next a-vertex, and the earlier introduced vertex.

Keeping these transports in one theorem prevents dependent carrier
equalities from obscuring the graph-theoretic part of the remaining proof.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- Coordinate identities for three consecutive alternating deformation
steps, all expressed through the labeling before the earliest step. -/
theorem three_step_alternating_coordinates
    {k : Nat} (D : ConcretePathDeformation O Cprime)
    (A : D.AlternatingLabelingSequence k)
    {earlier previous current : Fin D.deformation.stepCount}
    (hep : earlier.val + 1 = previous.val)
    (hpc : previous.val + 1 = current.val) :
    A.labeling previous =
        (A.labeling earlier).deform (A.cloneAt earlier) ∧
      A.removedAIndex previous =
        (A.labeling earlier).next (A.removedAIndex earlier) ∧
      (D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex =
        (A.labeling earlier).a
          ((A.labeling earlier).next (A.removedAIndex earlier)) ∧
      (A.labeling previous).a (A.removedAIndex earlier) =
        (D.deformation.step earlier).introduced ∧
      A.removedAIndex current =
        (A.labeling previous).next (A.removedAIndex previous) := by
  have htransport :
      A.labeling previous =
        (A.labeling earlier).deform (A.cloneAt earlier) :=
    A.transport_eq hep
  have hpreviousIndex :
      A.removedAIndex previous =
        (A.labeling earlier).next (A.removedAIndex earlier) :=
    A.removed_index_next hep
  have hpreviousRemoved :
      (D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex =
        (A.labeling earlier).a
          ((A.labeling earlier).next (A.removedAIndex earlier)) := by
    calc
      (D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex =
          (A.labeling previous).a (A.removedAIndex previous) :=
        A.removed_eq previous
      _ = ((A.labeling earlier).deform (A.cloneAt earlier)).a
          ((A.labeling earlier).next (A.removedAIndex earlier)) := by
        rw [htransport, hpreviousIndex]
      _ = (A.labeling earlier).a
          ((A.labeling earlier).next (A.removedAIndex earlier)) := by
        apply EvenHoleLabeling.deform_a_away
        exact (A.labeling earlier).next_ne (A.removedAIndex earlier)
  have hearlierIntroduced :
      (A.labeling previous).a (A.removedAIndex earlier) =
        (D.deformation.step earlier).introduced := by
    rw [htransport]
    exact EvenHoleLabeling.deform_a_at
      (A.labeling earlier) (A.cloneAt earlier)
  exact ⟨htransport, hpreviousIndex, hpreviousRemoved,
    hearlierIntroduced, A.removed_index_next hpc⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
