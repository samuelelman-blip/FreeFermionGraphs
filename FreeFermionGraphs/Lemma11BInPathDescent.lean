import FreeFermionGraphs.Lemma11BDescentBranches

/-!
# Lemma 11(b): previous-step descent in the in-path branch

In the first branch of the paper, an in-path dependent vertex at step `s`
produces a common-`C_b` Definition 20 witness at exactly step `s - 1`.
The overlap-index argument already proves that an in-path dependent vertex
cannot occur at step zero.

Consequently the concrete previous-step witness automatically has a
strictly smaller index and supplies the abstract in-path descent rule.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The paper's immediate-predecessor construction in the in-path branch. -/
def InPathPreviousStepCommonNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt s →
    u ∈ Set.range D.path.vertex →
    ¬D.path.AnticommutesWith u →
    ∃ u' w : V,
      D.Definition20DependentAt (s - 1) u' ∧
      w ∈ O.Cb ∧
      G.Adj u' w ∧
      G.Adj u w

/-- The previous-step construction is strict because every in-path
dependent vertex has positive deformation index. -/
theorem inPathStrictDefinition20CommonNeighborRule_of_previousStep
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hprevious : D.InPathPreviousStepCommonNeighborRule) :
    D.InPathStrictDefinition20CommonNeighborRule := by
  intro s u hu huPath hnotAnti
  obtain ⟨t, _ht, hsucc, _huRemoved⟩ :=
    D.dependent_mem_path_eq_previous_removed L hu huPath
  have hsPos : 0 < s := by
    omega
  obtain ⟨u', w, hu', hw, hu'w, huw⟩ :=
    hprevious hu huPath hnotAnti
  exact ⟨s - 1, u', w, by omega, hu', hw, hu'w, huw⟩

/-- Branch-local data with the in-path descent field reduced to the exact
previous-step construction in the paper. -/
structure Lemma11BPreviousStepBranchData
    (D : ConcretePathDeformation O Cprime) : Prop where
  inPathDegree :
    D.InPathAdditionalNeighborRule
  outsidePathDegree :
    D.OutsidePathCCNeighborIndexRule
  inPathPreviousStep :
    D.InPathPreviousStepCommonNeighborRule
  outsidePathDescent :
    D.OutsidePathStrictDefinition20CommonNeighborRule

/-- Convert the previous-step package to the four geometric branch rules. -/
theorem geometricBranchData_of_previousStep
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (B : D.Lemma11BPreviousStepBranchData) :
    D.Lemma11BGeometricBranchData where
  inPathDegree := B.inPathDegree
  outsidePathDegree := B.outsidePathDegree
  inPathDescent :=
    D.inPathStrictDefinition20CommonNeighborRule_of_previousStep
      L B.inPathPreviousStep
  outsidePathDescent := B.outsidePathDescent

/-- Lemma 11(b) with in-path descent reduced to the paper's explicit
previous-step witness. -/
theorem lemma11b_of_previousStepBranchData
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (B : D.Lemma11BPreviousStepBranchData)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact D.lemma11b_of_geometricBranchData
    M L hclaw hInitialEven hcolors
    (D.geometricBranchData_of_previousStep L B)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
