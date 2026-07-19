import FreeFermionGraphs.Lemma11BInPathDescent

/-!
# Lemma 11(b): one/two-step descent outside the active path

The outside-path case of the paper first excludes a commuting dependent
vertex at step zero. At every positive step it then constructs a common
`C_b` neighbor with a Definition 20 vertex either one or two steps
earlier.

Both alternatives are automatically strict. This module turns those two
paper-level facts into the remaining outside-path strict descent rule.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The outside-path base case: every dependent vertex at step zero
anticommutes with the active path. -/
def OutsidePathBaseAnticommutesRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃u : V⦄,
    u ∈ D.dependentAt 0 →
    u ∉ Set.range D.path.vertex →
    D.path.AnticommutesWith u

/-- At a positive outside-path step, the paper constructs one common
`C_b` neighbor with a Definition 20 vertex one or two steps earlier. -/
def OutsidePathOneOrTwoStepCommonNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt (Nat.succ s) →
    u ∉ Set.range D.path.vertex →
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

/-- The base exclusion and one/two-step construction imply strict descent
throughout the outside-path branch. -/
theorem outsidePathStrictDefinition20CommonNeighborRule_of_oneOrTwoStep
    (D : ConcretePathDeformation O Cprime)
    (hbase : D.OutsidePathBaseAnticommutesRule)
    (hstep : D.OutsidePathOneOrTwoStepCommonNeighborRule) :
    D.OutsidePathStrictDefinition20CommonNeighborRule := by
  intro s u hu huOutside hnotAnti
  cases s with
  | zero =>
      exact (hnotAnti (hbase hu huOutside)).elim
  | succ s =>
      obtain ⟨w, hw, huw, hbranch⟩ :=
        hstep hu huOutside hnotAnti
      rcases hbranch with hone | htwo
      · obtain ⟨u', hu', hu'w⟩ := hone
        exact ⟨s, u', w, by omega, hu', hw, hu'w, huw⟩
      · obtain ⟨t, hts, u', hu', hu'w⟩ := htwo
        exact ⟨t, u', w, by omega, hu', hw, hu'w, huw⟩

/-- All remaining branch data, with both descent branches reduced to the
exact local step patterns in the paper. -/
structure Lemma11BOneOrTwoStepBranchData
    (D : ConcretePathDeformation O Cprime) : Prop where
  inPathDegree :
    D.InPathAdditionalNeighborRule
  outsidePathDegree :
    D.OutsidePathCCNeighborIndexRule
  inPathPreviousStep :
    D.InPathPreviousStepCommonNeighborRule
  outsidePathBase :
    D.OutsidePathBaseAnticommutesRule
  outsidePathOneOrTwoStep :
    D.OutsidePathOneOrTwoStepCommonNeighborRule

/-- Convert the paper's local step patterns to the previous branch package. -/
theorem previousStepBranchData_of_oneOrTwoStep
    (D : ConcretePathDeformation O Cprime)
    (B : D.Lemma11BOneOrTwoStepBranchData) :
    D.Lemma11BPreviousStepBranchData where
  inPathDegree := B.inPathDegree
  outsidePathDegree := B.outsidePathDegree
  inPathPreviousStep := B.inPathPreviousStep
  outsidePathDescent :=
    D.outsidePathStrictDefinition20CommonNeighborRule_of_oneOrTwoStep
      B.outsidePathBase B.outsidePathOneOrTwoStep

/-- Lemma 11(b) from the degree constructions, the in-path previous-step
witness, and the outside-path base plus one/two-step recursion. -/
theorem lemma11b_of_oneOrTwoStepBranchData
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (B : D.Lemma11BOneOrTwoStepBranchData)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact D.lemma11b_of_previousStepBranchData
    M L hclaw hInitialEven hcolors
    (D.previousStepBranchData_of_oneOrTwoStep B)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
