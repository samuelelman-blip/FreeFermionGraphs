import FreeFermionGraphs.Lemma11BDefinition20CommonNeighbor

/-!
# Lemma 11(b): indexed final-neighbor certificates

The degree-four obstruction is naturally expressed using three vertices of
the final indexed hole. Naming their indices makes carrier membership
automatic, and injectivity of the hole labeling turns distinct indices into
distinct vertices.

This removes six pieces of set/equality bookkeeping from each local branch
of the paper's case analysis.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Three indexed final-hole neighbors giving the introduced-class
obstruction. Carrier membership is encoded by the index types themselves. -/
def HasCCIsolatedFinalNeighborIndexData
    (D : ConcretePathDeformation O Cprime) (u : V) : Prop :=
  ∃ p q r : Fin D.finalHole.card,
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    G.Adj u (D.finalHole.vertex p) ∧
    G.Adj u (D.finalHole.vertex q) ∧
    G.Adj u (D.finalHole.vertex r) ∧
    D.finalHole.vertex p ∈ O.Cc ∧
    D.finalHole.vertex q ∈ O.Cc ∧
    ¬G.Adj (D.finalHole.vertex p) (D.finalHole.vertex r)

/-- Indexed neighbor data supplies the named-vertex certificate. -/
theorem hasCCIsolatedFinalNeighborData_of_indexData
    (D : ConcretePathDeformation O Cprime)
    {u : V}
    (hdata : D.HasCCIsolatedFinalNeighborIndexData u) :
    D.HasCCIsolatedFinalNeighborData u := by
  obtain ⟨p, q, r, hpq, hpr, hqr,
    hup, huq, hur, hpCc, hqCc, hnpr⟩ := hdata
  refine
    ⟨D.finalHole.vertex p,
      D.finalHole.vertex q,
      D.finalHole.vertex r,
      ?_, ?_, ?_,
      ⟨p, rfl⟩, ⟨q, rfl⟩, ⟨r, rfl⟩,
      hup, huq, hur, hpCc, hqCc, hnpr⟩
  · intro hpqVertex
    exact hpq (D.finalHole.injective hpqVertex)
  · intro hprVertex
    exact hpr (D.finalHole.injective hprVertex)
  · intro hqrVertex
    exact hqr (D.finalHole.injective hqrVertex)

/-- Concrete Lemma 11(b) with the local degree branch reduced to three
indexed final-hole neighbors. -/
theorem lemma11b_of_initialEven_ccNeighborIndices_baseParity_and_definition20CommonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (hindices : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalNeighborIndexData u)
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
    D.lemma11b_of_initialEven_ccNeighborData_baseParity_and_definition20CommonNeighbors
      M hclaw hInitialEven hcolors
      (by
        intro s' u' hu' hcomm'
        exact D.hasCCIsolatedFinalNeighborData_of_indexData
          (hindices hu' hcomm'))
      horder hopposite hraw hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
