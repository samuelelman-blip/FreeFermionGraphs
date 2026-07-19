import FreeFermionGraphs.Lemma11BBranchAssembly

/-!
# Lemma 11(b): branchwise strict descent

The recursive part of the paper follows the same geometric split as the
degree argument. An in-path overlap vertex has a direct preceding-step
construction, while an outside-path vertex is handled by the longer claw
case analysis.

This module separates those obligations and then recombines them into the
strict Definition 20 rule consumed by the well-founded descent theorem.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A strict Definition 20 common-neighbor witness for one dependent
vertex. -/
def HasStrictDefinition20CommonNeighbor
    (D : ConcretePathDeformation O Cprime)
    (s : Nat) (u : V) : Prop :=
  ∃ s' : Nat, ∃ u' w : V,
    s' < s ∧
    D.Definition20DependentAt s' u' ∧
    w ∈ O.Cb ∧
    G.Adj u' w ∧
    G.Adj u w

/-- Strict descent in the overlap-aware in-path branch. -/
def InPathStrictDefinition20CommonNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt s →
    u ∈ Set.range D.path.vertex →
    ¬D.path.AnticommutesWith u →
    D.HasStrictDefinition20CommonNeighbor s u

/-- Strict descent in the outside-path branch. -/
def OutsidePathStrictDefinition20CommonNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt s →
    u ∉ Set.range D.path.vertex →
    ¬D.path.AnticommutesWith u →
    D.HasStrictDefinition20CommonNeighbor s u

/-- The two branchwise constructions give the global strict Definition 20
descent rule. -/
theorem strictDefinition20CommonNeighborRule_of_branches
    (D : ConcretePathDeformation O Cprime)
    (hinPath : D.InPathStrictDefinition20CommonNeighborRule)
    (houtsidePath : D.OutsidePathStrictDefinition20CommonNeighborRule) :
    D.StrictDefinition20CommonNeighborRule := by
  intro s u hu hnotAnti
  by_cases huPath : u ∈ Set.range D.path.vertex
  · exact hinPath hu huPath hnotAnti
  · exact houtsidePath hu huPath hnotAnti

/-- The four remaining graph-local obligations, separated according to the
two branches of the paper. -/
structure Lemma11BGeometricBranchData
    (D : ConcretePathDeformation O Cprime) : Prop where
  inPathDegree :
    D.InPathAdditionalNeighborRule
  outsidePathDegree :
    D.OutsidePathCCNeighborIndexRule
  inPathDescent :
    D.InPathStrictDefinition20CommonNeighborRule
  outsidePathDescent :
    D.OutsidePathStrictDefinition20CommonNeighborRule

/-- Lemma 11(b) from the four branch-local geometric constructions. -/
theorem lemma11b_of_geometricBranchData
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (B : D.Lemma11BGeometricBranchData)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u := by
  exact
    D.lemma11b_of_inPathAdditional_outsidePathIndices_and_strictDescent
      M L hclaw hInitialEven hcolors
      B.inPathDegree B.outsidePathDegree
      (D.strictDefinition20CommonNeighborRule_of_branches
        B.inPathDescent B.outsidePathDescent)
      hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
