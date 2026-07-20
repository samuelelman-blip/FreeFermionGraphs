import FreeFermionGraphs.Lemma11BFinalHoleColors

/-!
# Lemma 11(b): an existential Definition 20 predecessor neighbor

The paper's recursive step constructs one earlier dependent vertex in the
same `C_b ∪ C'_d` component as the current vertex. It is enough to exhibit
one common `C_b` neighbor. The previous interface required the construction
to work for every `C_b` neighbor of the current vertex.

This module replaces that unnecessarily strong universal rule by the
existential common-neighbor statement used in the proof.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The paper-level recursive step: a commuting dependent vertex at
`s + 1` shares some `C_b` neighbor with a Definition 20 vertex either
one or two steps earlier. -/
def OneOrTwoStepDefinition20CommonNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt (Nat.succ s) →
    ¬D.path.AnticommutesWith u →
    ∃ w : V,
      w ∈ O.Cb ∧
      G.Adj u w ∧
      ((∃ u' : V,
          D.Definition20DependentAt s u' ∧
            G.Adj u' w) ∨
        (∃ t : Nat, Nat.succ t = s ∧
          ∃ u' : V,
            D.Definition20DependentAt t u' ∧
              G.Adj u' w))

/-- An existential Definition 20 common-neighbor witness supplies the
one/two-step local predecessor rule. -/
theorem oneOrTwoStepCommonBNeighborRule_of_definition20CommonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (hraw : D.OneOrTwoStepDefinition20CommonNeighborRule) :
    D.OneOrTwoStepCommonBNeighborRule := by
  intro s u hu hnotAnti
  obtain ⟨w, hw, huw, hbranch⟩ := hraw hu hnotAnti
  rcases hbranch with hone | htwo
  · obtain ⟨u', hu', hu'w⟩ := hone
    exact ⟨s, u', w, Or.inl rfl,
      (D.mem_dependentAt_iff_definition20).2 hu',
      hw, hu'w, huw⟩
  · obtain ⟨t, hts, u', hu', hu'w⟩ := htwo
    exact ⟨t, u', w, Or.inr hts,
      (D.mem_dependentAt_iff_definition20).2 hu',
      hw, hu'w, huw⟩

/-- The reduced base parity theorem and one existential shared neighbor
give the complete common-`C_b` predecessor rule. -/
theorem commonBPredecessorRule_of_baseParity_and_definition20CommonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hraw : D.OneOrTwoStepDefinition20CommonNeighborRule) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith := by
  have hlocal : D.OneOrTwoStepCommonBNeighborRule :=
    D.oneOrTwoStepCommonBNeighborRule_of_definition20CommonNeighbors hraw
  have htyped :
      O.OneOrTwoStepCommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith :=
    D.oneOrTwoStepCommonBPredecessorRule_of_commonNeighbors
      M hlocal
  have hsucc :
      O.SuccessorCommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith :=
    O.successorCommonBPredecessorRule_of_oneOrTwoStep
      .ac D.dependentAt D.path.AnticommutesWith htyped
  exact O.commonBPredecessorRule_of_base_and_successor
    .ac D.dependentAt D.path.AnticommutesWith
    (fun {_u} hu =>
      D.baseDependentAnticommutes_of_baseParity
        M hclaw horder hopposite hu)
    hsucc

/-- Concrete Lemma 11(b) with both local interfaces reduced: the degree
branch names only its three final-hole neighbors, while the recursive branch
exhibits only one shared `C_b` neighbor and its earlier Definition 20
vertex. -/
theorem lemma11b_of_initialEven_ccNeighborData_baseParity_and_definition20CommonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (hneighbors : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalNeighborData u)
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
    D.lemma11b_of_concretePathDeformation_of_ccIsolatedFinalTriples
      M hclaw
      (by
        intro s' u' hu'
        exact O.pairingSideSeparated_of_exactlyOne
          (M.dependent_exactlyOne hcolors hu'))
      (D.finalHole_even_of_initialHole_even hInitialEven)
      (by
        intro s' u' hu' hcomm'
        exact D.hasCCIsolatedFinalTriple_of_neighborData
          M hcolors hu' (hneighbors hu' hcomm'))
      (D.commonBPredecessorRule_of_baseParity_and_definition20CommonNeighbors
        M hclaw horder hopposite hraw)
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
