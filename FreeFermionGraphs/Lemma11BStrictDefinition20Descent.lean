import FreeFermionGraphs.Lemma11BFinalNeighborIndices

/-!
# Lemma 11(b): strict Definition 20 descent

The paper proves that every commuting dependent vertex has an earlier
Definition 20 vertex in the same complementary pairing component. Stating
that conclusion with a strict index inequality also contains the base case:
there cannot be a commuting dependent vertex at index zero.

This module converts the strict raw common-neighbor witness directly into
the predecessor rule, removing the separate path-order and opposite-endpoint
base assumptions from the final Lemma 11(b) interface.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Every commuting dependent vertex shares a `C_b` neighbor with a
Definition 20 vertex at a strictly earlier deformation index. -/
def StrictDefinition20CommonNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt s →
    ¬D.path.AnticommutesWith u →
    ∃ s' : Nat, ∃ u' w : V,
      s' < s ∧
      D.Definition20DependentAt s' u' ∧
      w ∈ O.Cb ∧
      G.Adj u' w ∧
      G.Adj u w

/-- Mechanical color membership upgrades a strict Definition 20 witness to
the typed common-`C_b) predecessor rule. -/
theorem commonBPredecessorRule_of_strictDefinition20CommonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hraw : D.StrictDefinition20CommonNeighborRule) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith := by
  intro s u hu hcomm
  obtain ⟨s', u', w, hs', hu'Raw, hw, hu'w, huw⟩ :=
    hraw hu hcomm
  have hu' : u' ∈ D.dependentAt s' :=
    (D.mem_dependentAt_iff_definition20).2 hu'Raw
  refine ⟨s', u', w, hs', hu', ?_, ?_, hw, hu'w, huw⟩
  · change u' ∈ O.Cd
    exact M.dependent_mem_cd hu'
  · change u ∈ O.Cd
    exact M.dependent_mem_cd hu

/-- Concrete Lemma 11(b) with base anticommutation absorbed into strict
Definition 20 descent. The final interface no longer requires either the
Definition 19 index arithmetic or a separate opposite-endpoint nonedge. -/
theorem lemma11b_of_initialEven_ccNeighborIndices_and_strictDefinition20Descent
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (hindices : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalNeighborIndexData u)
    (hraw : D.StrictDefinition20CommonNeighborRule)
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
          M hcolors hu'
          (D.hasCCIsolatedFinalNeighborData_of_indexData
            (hindices hu' hcomm')))
      (D.commonBPredecessorRule_of_strictDefinition20CommonNeighbors
        M hraw)
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
