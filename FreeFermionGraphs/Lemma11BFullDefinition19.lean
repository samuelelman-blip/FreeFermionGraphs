import FreeFermionGraphs.Lemma11BDefinition19PathDescent

/-!
# Lemma 11(b): full Definition 19 neighbourhood data

The existing formal Definition 19 data records the concrete deformation,
the alternating holes, and the order of their path indices.  This module
packages the unchanged prime hole needed by the recursive proof.  The
in-path, ordinary outside, and exceptional six-cycle branches are all
theorems, so the package has no residual graph-theoretic field.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The unchanged prime-hole data from the full Definition 19
neighbourhood.  All recursive cases are derived from it. -/
structure FullDefinition19NeighborhoodData
    (D : ConcretePathDeformation O Cprime) where
  primeHalfLength : Nat
  primeHole : D.PrimeAlternatingHoleData primeHalfLength

namespace FullDefinition19NeighborhoodData

variable {D : ConcretePathDeformation O Cprime}

/-- The full data supplies strict Definition 20 descent in the same
fixed-pairing path component. -/
theorem strictDefinition20SharesPathRule
    {k : Nat}
    (F : D.FullDefinition19NeighborhoodData)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (hcycle : A.HasFullCyclicOrder)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency) :
    D.StrictDefinition20SharesPathRule :=
  D.strictDefinition20SharesPathRule_of_alternating_primeHole
    M A F.primeHole hcycle L hclaw hcolors horder hopposite

end FullDefinition19NeighborhoodData

/-- Final form of Lemma 11(b) from the complete Definition 19
neighbourhood package, with every recursive branch discharged. -/
theorem lemma11b_of_fullDefinition19NeighborhoodData
    {k : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (F : D.FullDefinition19NeighborhoodData)
    (hcycle : A.HasFullCyclicOrder)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact
    D.lemma11b_of_alternatingLabelingSequence_and_primeHole
      M A F.primeHole hcycle L hclaw hInitialEven hcolors horder hopposite
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
