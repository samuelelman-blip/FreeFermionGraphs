import FreeFermionGraphs.Lemma11BExceptionalLaterAgreement
import FreeFermionGraphs.Lemma11BInPathFinalDegree
import FreeFermionGraphs.Lemma11BConsolidatedDescent

/-!
# Lemma 11(b): complete alternating-deformation proof

The in-path degree calculation and the alternating outside-path calculation
now cover every dependent vertex.  Combining that degree-four rule with the
strict Definition 20 descent proves both conclusions of Lemma 11(b): final
degree four and an earlier anticommuting witness in the unique pairing path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The direct final-degree rule.  Vertices on the Definition 19 path use
the replacement-degree recurrence; vertices outside it use the alternating
hole labels and the three half-length cases. -/
theorem finalDegreeFourRule_of_alternating
    {k : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (hcycle : A.HasFullCyclicOrder)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  intro s u hu hnotAnti
  by_cases huPath : u ∈ Set.range D.path.vertex
  · exact D.dependent_mem_path_finalDegree_eq_four L hu huPath
  · exact
      D.outside_finalDegree_eq_four_of_alternating
        M A hcycle L hclaw hInitialEven hcolors horder hopposite
        hu huPath hnotAnti

/-- Lemma 11(b) for an alternating Definition 19 deformation.  The only
remaining paper-level inputs are the encoded alternating hole sequence,
its cyclic order, and the local one/two-step Definition 20 construction. -/
theorem lemma11b_of_alternatingLabelingSequence_and_definition20
    {k : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (hcycle : A.HasFullCyclicOrder)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hraw : D.OneOrTwoStepDefinition20CommonNeighborRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact
    D.lemma11b_of_concretePathDeformation
      M hclaw D.finalDegree
      (D.finalDegreeFourRule_of_alternating
        M A hcycle L hclaw hInitialEven hcolors horder hopposite)
      (D.commonBPredecessorRule_of_strictDefinition20CommonNeighbors
        M
        (D.strictDefinition20CommonNeighborRule_of_baseParity_and_oneOrTwoStep
          M hclaw horder hopposite hraw))
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
