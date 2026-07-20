import FreeFermionGraphs.Lemma11BPrimeHoleInPathDescent

/-!
# Lemma 11(b): full Definition 19 neighbourhood data

The existing formal Definition 19 data records the concrete deformation,
the alternating holes, and the order of their path indices. The paper also
uses a global neighbourhood-recursion fact for dependent vertices outside
the active pairing path. That fact is not derivable from the abbreviated
path-order interface alone.

This module makes that missing paper-level data explicit. Given the prime
hole and the outside-path recursion, the in-path predecessor is constructed
from the prime hole and the final conclusion of Lemma 11(b) follows without
a separate raw descent hypothesis.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The full neighbourhood data from Definition 19 needed by the recursive
part of Lemma 11(b).

'outsideOneOrTwoStep' is deliberately a field rather than an axiom: it is
the precise remaining graph-theoretic consequence of the paper's Definition
19 setup which must be supplied when that setup is formalized in full. -/
structure FullDefinition19NeighborhoodData
    (D : ConcretePathDeformation O Cprime) where
  primeHalfLength : Nat
  primeHole : D.PrimeAlternatingHoleData primeHalfLength
  outsideOneOrTwoStep : D.OutsidePathOneOrTwoStepCommonNeighborRule

namespace FullDefinition19NeighborhoodData

variable {D : ConcretePathDeformation O Cprime}

/-- The full data supplies the global one/two-step Definition 20 rule:
the prime-hole construction discharges the in-path case, and the explicit
neighbourhood recursion discharges the outside-path case. -/
theorem oneOrTwoStepDefinition20CommonNeighborRule
    (F : D.FullDefinition19NeighborhoodData)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree) :
    D.OneOrTwoStepDefinition20CommonNeighborRule := by
  exact
    D.oneOrTwoStepDefinition20CommonNeighborRule_of_primeHole_and_outside
      M F.primeHole L hclaw F.outsideOneOrTwoStep

end FullDefinition19NeighborhoodData

/-- Final form of Lemma 11(b) from the complete Definition 19
neighbourhood package. In particular, callers no longer pass a separate
unstructured one/two-step predecessor rule. -/
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
    D.lemma11b_of_alternatingLabelingSequence_and_definition20
      M A hcycle L hclaw hInitialEven hcolors horder hopposite
      (F.oneOrTwoStepDefinition20CommonNeighborRule M L hclaw)
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
