import FreeFermionGraphs.Lemma11BPrimeHoleInPathDescent
import FreeFermionGraphs.Lemma11BDefinition19OutsideRecursion

/-!
# Lemma 11(b): full Definition 19 neighbourhood data

The existing formal Definition 19 data records the concrete deformation,
the alternating holes, and the order of their path indices. The paper's
remaining recursive argument is used only after those data produce its
consecutive-step local configuration.

This module packages the fixed prime hole and that local recursion. The
in-path predecessor is constructed from the prime hole; the local rule is
then lifted to the global outside-path recursion by the already formalized
Definition 19 mechanics.
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

The local field is deliberately exposed: it is the remaining
graph-theoretic case analysis in the paper, stated only after the complete
consecutive-step configuration has been constructed. -/
structure FullDefinition19NeighborhoodData
    (D : ConcretePathDeformation O Cprime) where
  primeHalfLength : Nat
  primeHole : D.PrimeAlternatingHoleData primeHalfLength
  outsideConsecutiveOneOrTwoStep :
    D.OutsideConsecutiveOneOrTwoStepRule

namespace FullDefinition19NeighborhoodData

variable {D : ConcretePathDeformation O Cprime}

/-- The full data supplies the global one/two-step Definition 20 rule:
the prime-hole construction discharges the in-path case, while the local
consecutive-step recursion discharges the outside-path case. -/
theorem oneOrTwoStepDefinition20CommonNeighborRule
    {k : Nat}
    (F : D.FullDefinition19NeighborhoodData)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency) :
    D.OneOrTwoStepDefinition20CommonNeighborRule := by
  have houtside : D.OutsidePathOneOrTwoStepCommonNeighborRule :=
    D.outsidePathOneOrTwoStepCommonNeighborRule_of_consecutiveConfiguration
      M A L hclaw horder hopposite
      F.outsideConsecutiveOneOrTwoStep
  exact
    D.oneOrTwoStepDefinition20CommonNeighborRule_of_primeHole_and_outside
      M F.primeHole L hclaw houtside

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
      (F.oneOrTwoStepDefinition20CommonNeighborRule
        M A L hclaw horder hopposite)
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
