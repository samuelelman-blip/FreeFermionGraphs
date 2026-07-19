import FreeFermionGraphs.Lemma11BHalfLengthThree
import FreeFermionGraphs.Lemma11BInPathDegreeRecurrence

/-!
# Lemma 11(b): degree recurrence in the exceptional six-cycle branch

The half-length-three obstruction produces four distinct neighbors on the
hole immediately before the preceding replacement.  If the dependent
vertex already neighbors that step's introduced vertex, the ordinary
outside-path branch applies.  Otherwise the preceding step removes a
neighbor and introduces a nonneighbor, so the degree drops from four to
three.  The current dependent step then introduces a neighbor in place of a
nonneighbor and raises the degree back to four.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- In the six-cycle branch, either the preceding introduced path vertex is
a neighbor, or the current deformation has already restored external degree
four. -/
theorem previous_introduced_or_current_degreeAfter_eq_four_of_halfLength_three
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence 3)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    ∃ previous : Fin D.deformation.stepCount,
      previous.val + 1 = s ∧
        (G.Adj u (D.deformation.step previous).introduced ∨
          (D.deformation.step
            ⟨s, D.index_lt_of_mem_dependentAt hu⟩).degreeAfter u = 4) := by
  obtain ⟨previous, hprevious, hbranch⟩ :=
    D.previous_introduced_or_four_previous_neighbors_of_halfLength_three
      M A L hclaw horder hopposite hu huOutside hnotAnti
  rcases hbranch with huPreviousIntroduced | hfour
  · exact ⟨previous, hprevious, Or.inl huPreviousIntroduced⟩
  · by_cases huPreviousIntroduced :
        G.Adj u (D.deformation.step previous).introduced
    · exact ⟨previous, hprevious, Or.inl huPreviousIntroduced⟩
    · have hs : s < D.deformation.stepCount :=
        D.index_lt_of_mem_dependentAt hu
      let current : Fin D.deformation.stepCount := ⟨s, hs⟩
      have hij : previous.val + 1 = current.val := by
        simpa [current] using hprevious
      obtain ⟨t, ht, hts, huRemovedAtT⟩ :=
        D.adj_previous_removed_of_outside_commuting
          M L hclaw horder hopposite hu huOutside hnotAnti
      have htp : (⟨t, ht⟩ : Fin D.deformation.stepCount) = previous := by
        apply Fin.ext
        omega
      have huPreviousRemoved :
          G.Adj u
            ((D.deformation.step previous).before.vertex
              (D.deformation.step previous).removedIndex) := by
        simpa only [htp] using huRemovedAtT
      have hEvenPrevious :
          Even (D.deformation.step previous).before.card := by
        rw [D.deformation.before_card_eq_first
          D.nonempty previous.val previous.isLt]
        simpa [initialHole, firstIndex] using hInitialEven
      have hbeforeFour :
          (D.deformation.step previous).before.externalDegree u = 4 :=
        (D.deformation.step previous).before.externalDegree_eq_four_of_even_card
          hclaw hEvenPrevious hfour
      have hpreviousAfterThree :
          (D.deformation.step previous).degreeAfter u = 3 := by
        have hdrop :
            (D.deformation.step previous).before.externalDegree u =
              (D.deformation.step previous).degreeAfter u + 1 := by
          simpa [ConcreteDeformationStep.degreeAfter,
            ConcreteDeformationStep.after] using
            IndexedInducedHole.SingleVertexDeformation.externalDegree_eq_deform_add_one
              (D.deformation.step previous).deformation
              huPreviousIntroduced huPreviousRemoved
        omega
      have hcurrentBeforeThree :
          (D.deformation.step current).degreeBefore u = 3 := by
        rw [← D.deformation.degreeAfter_eq_nextDegreeBefore
          (i := previous) (j := current) hij u]
        exact hpreviousAfterThree
      have huCurrent :
          u ∈ (D.deformation.step current).dependentSet := by
        simpa [current] using
          D.mem_step_dependentSet_of_mem_dependentAt hu
      have hcurrentAfterFour :
          (D.deformation.step current).degreeAfter u = 4 := by
        have hgain :=
          ConcreteDeformationStep.degreeAfter_eq_add_one_of_mem_dependentSet
            (D.deformation.step current) huCurrent
        omega
      exact
        ⟨previous, hprevious, Or.inr (by
          simpa [current] using hcurrentAfterFour)⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
