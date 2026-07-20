import FreeFermionGraphs.Lemma11BDefinition19PathDescent

/-!
# Lemma 11(b): integrated Definition 19 neighbourhood data

This module is the integration boundary for the formal proof.  It packages
the concrete deformation geometry, transported alternating holes, global
overlap-aware path order, unchanged prime hole, and the permitted cross-hole
color overlaps in one object.  Initial evenness and the older local path
order are derived from these fields.  The only boundary fact retained is
the opposite-endpoint nonedge used by the base application of Lemma 7.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- All data used by the integrated Lemma 11(b) proof for one Definition 19
path block.  In particular, `overlapColoring` admits the `C_a ∩ C'_d` and
`C_b ∩ C'_c` intersections present in the manuscript. -/
structure FullDefinition19NeighborhoodData
    (D : ConcretePathDeformation O Cprime) where
  halfLength : Nat
  mechanical : D.MechanicalData
  alternating : D.AlternatingLabelingSequence halfLength
  cyclicOrder : alternating.HasFullCyclicOrder
  pathOrder : Definition19GlobalOverlapPathOrder D
  primeHalfLength : Nat
  primeHole : D.PrimeAlternatingHoleData primeHalfLength
  overlapColoring : O.PrimeCarrierOverlapColored Cprime
  baseOppositeEndpoint : D.BaseOppositeEndpointNonadjacency

namespace FullDefinition19NeighborhoodData

variable {D : ConcretePathDeformation O Cprime}

/-- The full data supplies strict Definition 20 descent in the same
fixed-pairing path component. -/
theorem strictDefinition20SharesBDPathRule
    (F : D.FullDefinition19NeighborhoodData)
    (hclaw : G.IsClawFree) :
    D.StrictDefinition20SharesBDPathRule :=
  D.strictDefinition20SharesBDPathRule_of_alternating_primeHole
    F.mechanical F.alternating F.primeHole F.cyclicOrder
    F.pathOrder hclaw F.overlapColoring F.baseOppositeEndpoint

end FullDefinition19NeighborhoodData

/-- Final form of Lemma 11(b) from the complete Definition 19
neighbourhood package, with every recursive branch discharged. -/
theorem lemma11b_of_fullDefinition19NeighborhoodData
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19NeighborhoodData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniqueBDPath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact
    D.lemma11b_of_alternatingLabelingSequence_and_primeHole
      F.mechanical F.alternating F.primeHole F.cyclicOrder
      F.pathOrder hclaw F.overlapColoring F.baseOppositeEndpoint
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
