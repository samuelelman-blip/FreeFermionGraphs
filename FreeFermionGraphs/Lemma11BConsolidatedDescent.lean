import FreeFermionGraphs.Lemma11BOutsideDescent

/-!
# Lemma 11(b): consolidated Definition 20 descent

The previously formalized base-parity theorem already rules out a commuting
dependent vertex at index zero. The existing one/two-step Definition 20
common-neighbor rule already supplies a strict witness at every successor
index.

Thus no separate in-path or outside-path descent assumptions are necessary:
the same paper-level Definition 20 construction discharges strict descent
in both geometric branches.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Base parity and the one/two-step Definition 20 construction imply the
global strict common-neighbor rule directly. -/
theorem strictDefinition20CommonNeighborRule_of_baseParity_and_oneOrTwoStep
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hraw : D.OneOrTwoStepDefinition20CommonNeighborRule) :
    D.StrictDefinition20CommonNeighborRule := by
  intro s u hu hnotAnti
  cases s with
  | zero =>
      exact
        (hnotAnti
          (D.baseDependentAnticommutes_of_baseParity
            M hclaw horder hopposite hu)).elim
  | succ s =>
      obtain ⟨w, hw, huw, hbranch⟩ :=
        hraw hu hnotAnti
      rcases hbranch with hone | htwo
      · obtain ⟨u', hu', hu'w⟩ := hone
        exact ⟨s, u', w, by omega, hu', hw, hu'w, huw⟩
      · obtain ⟨t, hts, u', hu', hu'w⟩ := htwo
        exact ⟨t, u', w, by omega, hu', hw, hu'w, huw⟩

/-- Lemma 11(b) with every recursive assumption discharged by the existing
base-parity and Definition 20 interfaces. Only the two branch-local degree
constructions remain. -/
theorem lemma11b_of_degreeBranches_and_definition20
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (hinPath : D.InPathAdditionalNeighborRule)
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
  exact
    D.lemma11b_of_inPathAdditional_outsidePathIndices_and_strictDescent
      M L hclaw hInitialEven hcolors hinPath houtsidePath
      (D.strictDefinition20CommonNeighborRule_of_baseParity_and_oneOrTwoStep
        M hclaw horder hopposite hraw)
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
