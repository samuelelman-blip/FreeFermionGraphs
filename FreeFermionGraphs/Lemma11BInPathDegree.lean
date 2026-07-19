import FreeFermionGraphs.Lemma11BInPathFinalExternal

/-!
# Lemma 11(b): degree four in the in-path branch

The overlap-aware Definition 19 analysis now proves that an in-path
dependent vertex is outside the final hole without using exact global color
membership. Consequently, the three indexed final-hole neighbors from the
local claw-free obstruction immediately form the introduced-class isolated
triple used by the degree-four theorem.

This isolates the first branch of the paper's proof: when the dependent
vertex lies on the active path, final-hole externality is structural rather
than a consequence of a disjoint-coloring hypothesis.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- In the in-path branch, indexed final-neighbor data gives the
introduced-class isolated triple without any exact-coloring assumption. -/
theorem hasCCIsolatedFinalTriple_of_mem_path_and_indexData
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (hdata : D.HasCCIsolatedFinalNeighborIndexData u) :
    D.HasCCIsolatedFinalTriple u := by
  refine ⟨D.dependent_mem_path_not_mem_finalHole L hu huPath, ?_⟩
  exact D.hasCCIsolatedFinalNeighborData_of_indexData hdata

/-- Three indexed final-hole neighbors force degree four for an in-path
dependent vertex. Exact coloring of the prime carrier is not required. -/
theorem finalDegree_eq_four_of_mem_path_and_ccNeighborIndices
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (hdata : D.HasCCIsolatedFinalNeighborIndexData u) :
    D.finalDegree s u = 4 := by
  have htriple :
      D.HasCCIsolatedFinalTriple u :=
    D.hasCCIsolatedFinalTriple_of_mem_path_and_indexData
      L hu huPath hdata
  have hisolated :
      D.finalHole.HasIsolatedExternalNeighborTriple u :=
    D.hasIsolatedExternalNeighborTriple_of_ccFinalTriple
      M hu htriple
  have hEven : Even D.finalHole.card :=
    D.finalHole_even_of_initialHole_even hInitialEven
  simpa [finalDegree] using
    D.finalHole.externalDegree_eq_four_of_isolated_neighbor_triple
      hclaw hEven hisolated

/-- Family form of the in-path degree-four branch. -/
theorem finalDegreeFourRule_on_path_of_ccNeighborIndices
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hindices : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      u ∈ Set.range D.path.vertex →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalNeighborIndexData u) :
    ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      u ∈ Set.range D.path.vertex →
      ¬D.path.AnticommutesWith u →
      D.finalDegree s u = 4 := by
  intro s u hu huPath hnotAnti
  exact D.finalDegree_eq_four_of_mem_path_and_ccNeighborIndices
    M L hclaw hInitialEven hu huPath
    (hindices hu huPath hnotAnti)

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
