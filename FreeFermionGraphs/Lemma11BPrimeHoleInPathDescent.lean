import FreeFermionGraphs.Lemma11BComplete
import FreeFermionGraphs.Lemma11BOutsideDescent
import FreeFermionGraphs.Lemma11BInPathPreviousRemoval

/-!
# Lemma 11(b): the prime-hole predecessor in the in-path branch

The paper keeps the second even hole C' throughout the deformation.
When a dependent vertex lies on the active Definition 19 path, it is the
vertex removed at the preceding step.  The preceding introduced vertex has
one other neighbor on C'.  That other neighbor is nonadjacent to the removed
vertex, so it satisfies Definition 20 at the preceding step.

The existing single-step common-neighbor theorem then supplies a common
C_b neighbor of the two dependent vertices.  This discharges the in-path
part of the recursive descent rather than retaining it as an interface
assumption.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The unchanged prime even hole C', together with the fact that every
introduced Definition 19 vertex is an a-vertex of that hole. -/
structure PrimeAlternatingHoleData
    (D : ConcretePathDeformation O Cprime) (kPrime : Nat) where
  labeling : EvenHoleLabeling G kPrime
  carrier_eq : labeling.carrier = Cprime
  introducedIndex :
    ∀ i : Fin D.deformation.stepCount, Fin kPrime
  introduced_eq :
    ∀ i : Fin D.deformation.stepCount,
      labeling.a (introducedIndex i) =
        (D.deformation.step i).introduced

namespace PrimeAlternatingHoleData

variable {D : ConcretePathDeformation O Cprime} {kPrime : Nat}

/-- Every introduced vertex belongs to the prime-hole carrier. -/
theorem introduced_mem
    (P : D.PrimeAlternatingHoleData kPrime)
    (i : Fin D.deformation.stepCount) :
    (D.deformation.step i).introduced ∈ Cprime := by
  rw [← P.carrier_eq, ← P.introduced_eq i]
  exact P.labeling.a_mem_carrier (P.introducedIndex i)

/-- If a prime-hole vertex neighbors an introduced a-vertex, the other
b-neighbor of that a-vertex is distinct and nonadjacent to it. -/
theorem exists_other_prime_neighbor
    (P : D.PrimeAlternatingHoleData kPrime)
    (i : Fin D.deformation.stepCount)
    {u : V}
    (hu : u ∈ Cprime)
    (huIntroduced :
      G.Adj u (D.deformation.step i).introduced) :
    ∃ u' : V,
      u' ∈ Cprime ∧
      G.Adj u' (D.deformation.step i).introduced ∧
      u' ≠ u ∧
      ¬G.Adj u' u := by
  let C : EvenHoleLabeling G kPrime := P.labeling
  let r : Fin kPrime := P.introducedIndex i
  have hintroduced :
      C.a r = (D.deformation.step i).introduced := by
    simpa [C, r] using P.introduced_eq i
  have huCarrier : u ∈ C.carrier := by
    rw [P.carrier_eq]
    exact hu
  change u ∈ Set.range C.a ∪ Set.range C.b at huCarrier
  rcases huCarrier with ⟨q, hqu⟩ | ⟨q, hqu⟩
  · subst u
    have haa : G.Adj (C.a q) (C.a r) := by
      rw [hintroduced]
      exact huIntroduced
    exact (C.adj_aa q r haa).elim
  · subst u
    have hab : G.Adj (C.a r) (C.b q) := by
      rw [hintroduced]
      exact huIntroduced.symm
    rcases (C.adj_ab_iff r q).1 hab with hqr | hqr
    · subst q
      refine ⟨C.b (C.next r), ?_, ?_, ?_, ?_⟩
      · rw [← P.carrier_eq]
        exact C.b_mem_carrier (C.next r)
      · rw [← hintroduced]
        exact (C.adj_a_b_next r).symm
      · exact C.b_ne_next r
      · exact C.adj_bb (C.next r) r
    · subst q
      refine ⟨C.b r, ?_, ?_, ?_, ?_⟩
      · rw [← P.carrier_eq]
        exact C.b_mem_carrier r
      · rw [← hintroduced]
        exact (C.adj_a_b r).symm
      · exact (C.b_ne_next r).symm
      · exact C.adj_bb r (C.next r)

end PrimeAlternatingHoleData

/-- The prime-hole cycle and the concrete step geometry construct the
paper's immediate predecessor in the in-path branch. -/
theorem inPathPreviousStepCommonNeighborRule_of_primeHole
    {kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (P : D.PrimeAlternatingHoleData kPrime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree) :
    D.InPathPreviousStepCommonNeighborRule := by
  intro s u hu huPath _hnotAnti
  obtain ⟨t, ht, hts, huRemoved⟩ :=
    D.dependent_mem_path_eq_previous_removed L hu huPath
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  have huRemoved' :
      u =
        (D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex := by
    simpa [previous] using huRemoved
  let current : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huCurrent :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have huPrime : u ∈ Cprime :=
    ((ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huCurrent).1
  have huPreviousIntroduced :
      G.Adj u (D.deformation.step previous).introduced := by
    rw [huRemoved']
    exact
      (D.deformation.step previous).deformation.adj_clone.symm
  obtain ⟨u', hu'Prime, hu'Introduced, hu'NeU, hu'NotU⟩ :=
    P.exists_other_prime_neighbor
      previous huPrime huPreviousIntroduced
  have hu'NeRemoved :
      u' ≠
        (D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex := by
    rw [← huRemoved']
    exact hu'NeU
  have hu'NotRemoved :
      ¬G.Adj u'
        ((D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex) := by
    rw [← huRemoved']
    exact hu'NotU
  have hu'Previous :
      u' ∈ (D.deformation.step previous).dependentSet := by
    exact
      (ConcreteDeformationStep.mem_dependentSet
        (D.deformation.step previous)).2
        ⟨hu'Prime, hu'Introduced, hu'NeRemoved, hu'NotRemoved⟩
  have hu'Definition20 :
      D.Definition20DependentAt t u' := by
    refine ⟨ht, hu'Prime, ?_, ?_, ?_⟩
    · simpa [previous] using hu'Introduced
    · simpa [previous] using hu'NeRemoved
    · simpa [previous] using hu'NotRemoved
  obtain ⟨w, _hwBefore, hu'w, _hintroducedW,
      hremovedW, hwCb⟩ :=
    (D.deformation.step previous).dependent_commonNeighbor_mem_cb
      (M.stepGeometry previous) hclaw hu'Previous
      (M.outsideHole previous hu'Previous)
  have huw : G.Adj u w := by
    rw [huRemoved']
    exact hremovedW
  have htPred : t = s - 1 := by
    omega
  refine ⟨u', w, ?_, hwCb, hu'w, huw⟩
  simpa [htPred] using hu'Definition20

/-- The concrete in-path construction and the remaining outside-path
construction together imply the global one/two-step Definition 20 rule. -/
theorem oneOrTwoStepDefinition20CommonNeighborRule_of_primeHole_and_outside
    {kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (P : D.PrimeAlternatingHoleData kPrime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (houtside : D.OutsidePathOneOrTwoStepCommonNeighborRule) :
    D.OneOrTwoStepDefinition20CommonNeighborRule := by
  intro s u hu hnotAnti
  by_cases huPath : u ∈ Set.range D.path.vertex
  · obtain ⟨u', w, hu', hw, hu'w, huw⟩ :=
      (D.inPathPreviousStepCommonNeighborRule_of_primeHole
        M P L hclaw) hu huPath hnotAnti
    refine ⟨w, hw, huw, Or.inl ?_⟩
    exact ⟨u', by simpa using hu', hu'w⟩
  · exact houtside hu huPath hnotAnti

/-- Lemma 11(b) with the in-path Definition 20 predecessor discharged from
the prime even hole.  Only the outside-path recursive construction remains
as a local input. -/
theorem lemma11b_of_alternating_primeHole_and_outsideDefinition20
    {k kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (P : D.PrimeAlternatingHoleData kPrime)
    (hcycle : A.HasFullCyclicOrder)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (houtside : D.OutsidePathOneOrTwoStepCommonNeighborRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact
    D.lemma11b_of_alternatingLabelingSequence_and_definition20
      M A hcycle L hclaw hInitialEven hcolors horder hopposite
      (D.oneOrTwoStepDefinition20CommonNeighborRule_of_primeHole_and_outside
        M P L hclaw houtside)
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
