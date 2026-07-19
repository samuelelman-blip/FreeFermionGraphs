import FreeFermionGraphs.Lemma11BAlternatingLabelingSequence
import FreeFermionGraphs.Lemma11BOutsidePredecessorAdjacency

/-!
# Lemma 11(b): the outside-path consecutive-step configuration

For an outside-path commuting dependent vertex at step `s`, the previous
step exists and claw-freeness forces adjacency to its removed vertex.  The
transported alternating labels provide the paper's vertex `w_(s-1)`,
common to both introduced/removed pairs.  Definition 20 supplies adjacency
to the current introduced vertex and nonadjacency to the current removed
vertex.

This module assembles those facts into the precise local configuration used
by the remaining half-length case split in the paper.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The complete local configuration at an outside-path commuting step. -/
def OutsideConsecutiveConfiguration
    (D : ConcretePathDeformation O Cprime)
    (s : Nat) (u : V) : Prop :=
  ∃ hs : s < D.deformation.stepCount,
    ∃ previous : Fin D.deformation.stepCount,
      previous.val + 1 = s ∧
      ∃ common : V,
        common ∈
            Set.range (D.deformation.step previous).before.vertex ∧
        common ∈
            Set.range
              (D.deformation.step ⟨s, hs⟩).before.vertex ∧
        G.Adj (D.deformation.step previous).introduced common ∧
        G.Adj
            ((D.deformation.step previous).before.vertex
              (D.deformation.step previous).removedIndex)
            common ∧
        G.Adj
            (D.deformation.step ⟨s, hs⟩).introduced
            common ∧
        G.Adj
            ((D.deformation.step ⟨s, hs⟩).before.vertex
              (D.deformation.step ⟨s, hs⟩).removedIndex)
            common ∧
        common ∈ O.Cb ∧
        G.Adj u
            ((D.deformation.step previous).before.vertex
              (D.deformation.step previous).removedIndex) ∧
        G.Adj u
            (D.deformation.step ⟨s, hs⟩).introduced ∧
        ¬G.Adj u
            ((D.deformation.step ⟨s, hs⟩).before.vertex
              (D.deformation.step ⟨s, hs⟩).removedIndex)

/-- Mechanical Definition 19/20 data and the transported alternating
labeling construct the outside consecutive-step configuration. -/
theorem outsideConsecutiveConfiguration
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    {k : Nat}
    (A : D.AlternatingLabelingSequence k)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    D.OutsideConsecutiveConfiguration s u := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  obtain ⟨t, ht, hts, huPreviousRemoved⟩ :=
    D.adj_previous_removed_of_outside_commuting
      M L hclaw horder hopposite hu huOutside hnotAnti
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  have hij : previous.val + 1 = current.val := by
    dsimp [previous, current]
    omega
  obtain
      ⟨w, hwPrevious, hwCurrent,
        hwPreviousIntroduced, hwPreviousRemoved,
        hwCurrentIntroduced, hwCurrentRemoved, hwCb⟩ :=
    A.consecutiveFourCommonNeighborRule M hij
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  refine ⟨hs, previous, ?_, w,
    hwPrevious, ?_,
    hwPreviousIntroduced, hwPreviousRemoved,
    ?_, ?_, hwCb, ?_, ?_, ?_⟩
  · dsimp [previous]
    omega
  · simpa [current] using hwCurrent
  · simpa [current] using hwCurrentIntroduced
  · simpa [current] using hwCurrentRemoved
  · simpa [previous] using huPreviousRemoved
  · simpa [current] using hmem.2.1
  · simpa [current] using hmem.2.2.2

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
