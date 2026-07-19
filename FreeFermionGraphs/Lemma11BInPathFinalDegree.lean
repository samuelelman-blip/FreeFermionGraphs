import FreeFermionGraphs.Lemma11BInPathDegreeRecurrence

/-!
# Lemma 11(b): final degree in the in-path branch

The current-step recurrence gives degree four at the dependent vertex's own
step. Definition 19 shows that every strictly later replacement preserves
that degree. This module propagates the equality through the remaining
finite deformation chain and identifies its endpoint with the final hole.

Consequently the in-path degree branch of Lemma 11(b) is now completely
discharged and no longer requires an additional-neighbor assumption.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Once an in-path dependent vertex reaches degree four at its own step,
it has degree four after every later step. -/
theorem dependent_mem_path_later_degreeAfter_eq_four
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (n : Nat)
    (hsn : s ≤ n)
    (hn : n < D.deformation.stepCount) :
    (D.deformation.step ⟨n, hn⟩).degreeAfter u = 4 := by
  induction hsn with
  | refl =>
      simpa using
        D.dependent_mem_path_current_degreeAfter_eq_four L hu huPath
  | @step n hsn ih =>
      have hn' : n < D.deformation.stepCount := by omega
      let previous : Fin D.deformation.stepCount := ⟨n, hn'⟩
      let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
      have hij : previous.val + 1 = current.val := by
        rfl
      have hprevious :
          (D.deformation.step previous).degreeAfter u = 4 := by
        simpa [previous] using ih hn'
      have hcurrentBefore :
          (D.deformation.step current).degreeBefore u = 4 := by
        rw [← D.deformation.degreeAfter_eq_nextDegreeBefore
          (i := previous) (j := current) hij u]
        exact hprevious
      have hcurrentAfter :
          (D.deformation.step current).degreeAfter u =
            (D.deformation.step current).degreeBefore u :=
        D.dependent_mem_path_later_degreeAfter_eq_degreeBefore
          L hu huPath current (by
            change s < n + 1
            exact Nat.lt_succ_of_le hsn)
      calc
        (D.deformation.step ⟨n + 1, hn⟩).degreeAfter u =
            (D.deformation.step current).degreeAfter u := by
              rfl
        _ = (D.deformation.step current).degreeBefore u := hcurrentAfter
        _ = 4 := hcurrentBefore

/-- Every in-path dependent vertex has degree four in the final hole. -/
theorem dependent_mem_path_finalDegree_eq_four
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    D.finalDegree s u = 4 := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  have hlast : D.deformation.stepCount - 1 <
      D.deformation.stepCount := by
    omega
  have hsLast : s ≤ D.deformation.stepCount - 1 := by
    omega
  have hdegree :=
    D.dependent_mem_path_later_degreeAfter_eq_four
      L hu huPath (D.deformation.stepCount - 1) hsLast hlast
  simpa [finalDegree, finalHole, lastIndex,
    ConcreteDeformationStep.degreeAfter] using hdegree

/-- Assemble the final degree-four rule with the in-path branch proved
directly and only the outside-path index obstruction left as input. -/
theorem finalDegreeFourRule_of_directInPath_and_outsidePathIndices
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (houtsidePath : D.OutsidePathCCNeighborIndexRule) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  intro s u hu hnotAnti
  by_cases huPath : u ∈ Set.range D.path.vertex
  · exact D.dependent_mem_path_finalDegree_eq_four L hu huPath
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

/-- Lemma 11(b) with the complete in-path degree proof and consolidated
Definition 20 descent. The only remaining branch-local hypothesis is the
outside-path CC-neighbor index obstruction. -/
theorem lemma11b_of_outsidePathIndices_and_definition20
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (houtsidePath : D.OutsidePathCCNeighborIndexRule)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hraw : D.OneOrTwoStepDefinition20CommonNeighborRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact D.lemma11b_of_concretePathDeformation
    M hclaw D.finalDegree
    (D.finalDegreeFourRule_of_directInPath_and_outsidePathIndices
      M L hclaw hInitialEven hcolors houtsidePath)
    (D.commonBPredecessorRule_of_strictDefinition20CommonNeighbors
      M
      (D.strictDefinition20CommonNeighborRule_of_baseParity_and_oneOrTwoStep
        M hclaw horder hopposite hraw))
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
