import FreeFermionGraphs.Lemma11BInPathThirdNeighbor

/-!
# Lemma 11(b): assembly of the in-path and outside-path branches

The paper treats dependent vertices on the active path separately from
vertices outside it. The in-path branch now needs only one additional
isolated final neighbor, while the outside-path branch retains the general
three-index obstruction.

This module performs that case split and combines the resulting degree-four
rule with strict Definition 20 descent. Exact global coloring is used only
in the outside-path branch; structural externality handles the overlap-aware
in-path branch.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The residual degree certificate for dependent vertices outside the
active path. -/
def OutsidePathCCNeighborIndexRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt s →
    u ∉ Set.range D.path.vertex →
    ¬D.path.AnticommutesWith u →
    D.HasCCIsolatedFinalNeighborIndexData u

/-- Assemble the degree-four rule by splitting on membership in the active
path. -/
theorem finalDegreeFourRule_of_inPathAdditional_and_outsidePathIndices
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (hinPath : D.InPathAdditionalNeighborRule)
    (houtsidePath : D.OutsidePathCCNeighborIndexRule) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  intro s u hu hnotAnti
  by_cases huPath : u ∈ Set.range D.path.vertex
  · exact D.finalDegree_eq_four_of_mem_path_and_additionalNeighbor
      M L hclaw hInitialEven hu huPath
      (hinPath hu huPath hnotAnti)
  · have hdata :
        D.HasCCIsolatedFinalNeighborIndexData u :=
      houtsidePath hu huPath hnotAnti
    have htriple :
        D.HasCCIsolatedFinalTriple u :=
      D.hasCCIsolatedFinalTriple_of_neighborData
        M hcolors hu
        (D.hasCCIsolatedFinalNeighborData_of_indexData hdata)
    have hisolated :
        D.finalHole.HasIsolatedExternalNeighborTriple u :=
      D.hasIsolatedExternalNeighborTriple_of_ccFinalTriple
        M hu htriple
    have hEven : Even D.finalHole.card :=
      D.finalHole_even_of_initialHole_even hInitialEven
    simpa [finalDegree] using
      D.finalHole.externalDegree_eq_four_of_isolated_neighbor_triple
        hclaw hEven hisolated

/-- Lemma 11(b) with its two geometric degree branches separated exactly as
in the paper and its recursive conclusion supplied by strict Definition 20
descent. -/
theorem lemma11b_of_inPathAdditional_outsidePathIndices_and_strictDescent
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (hinPath : D.InPathAdditionalNeighborRule)
    (houtsidePath : D.OutsidePathCCNeighborIndexRule)
    (hdescent : D.StrictDefinition20CommonNeighborRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact D.lemma11b_of_concretePathDeformation
    M hclaw D.finalDegree
    (D.finalDegreeFourRule_of_inPathAdditional_and_outsidePathIndices
      M L hclaw hInitialEven hcolors hinPath houtsidePath)
    (D.commonBPredecessorRule_of_strictDefinition20CommonNeighbors
      M hdescent)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
