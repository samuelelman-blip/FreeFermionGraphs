import FreeFermionGraphs.ObstructionSearchTwoSidedCorollary11Side

/-!
# Two-sided Corollary 11

After the component-side reduction, the two compared blocks are concrete
Definition 19 histories in one common oriented fixed-pairing family.  The
existing history proof of Corollary 11 can therefore be applied in that
orientation, including the side-swapped presentation of two manuscript `bd`
blocks.

This module proves the no-shared-dependent-anticommuting-witness conclusion for
arbitrary two-sided history witnesses.  It does not assume or conclude path
ownership, search disjointness, terminal-hole geometry, or Lemma 14.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

namespace Lemma11AHistoryContext

/-- Corollary 11 for two concrete histories already presented in one common
orientation.

The common original hole, evenness, carrier colouring, and base common
neighbours are all derived from the two history contexts. -/
theorem noSharedDependentAnticommutingWitness_of_same_oriented_history
    {D E : ConcretePathDeformation O Cprime}
    (A : D.Lemma11AHistoryContext)
    (B : E.Lemma11AHistoryContext)
    (hOriginal : A.originalHole = B.originalHole)
    (hclaw : G.IsClawFree)
    (hpathNe :
      Set.range D.path.vertex ≠ Set.range E.path.vertex) :
    ¬SharedDependentAnticommutingWitness
      D.path E.path D.dependentAt E.dependentAt := by
  have hEven : Even A.originalHole.card :=
    A.originalHole_even
  have hcarrier :
      Set.range A.originalHole.vertex ⊆ O.Ca ∪ O.Cb :=
    A.originalHole_carrier_subset
  have hcommonD : O.BaseCommonNeighborOn D A.originalHole :=
    A.baseCommonNeighborOn_originalHole hclaw
  have hcommonE : O.BaseCommonNeighborOn E A.originalHole := by
    rw [hOriginal]
    exact B.baseCommonNeighborOn_originalHole hclaw
  exact noSharedDependentAnticommutingWitness_of_concreteBlocks
    D E A.currentData B.currentData A.originalHole hclaw hEven hcarrier
    hpathNe hcommonD hcommonE

end Lemma11AHistoryContext

end ConcretePathDeformation

namespace TwoSidedSearchPathHistoryWitness

/-- Full history-backed Corollary 11 on the two-sided interface.

A hypothetical shared witness first forces equal component sides.  Destructing
that side presents both blocks either in `O` or in `O.swapSides`, where the
same oriented-history theorem applies. -/
theorem noSharedDependentAnticommutingWitness
    {S T : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P Q : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    (B : TwoSidedSearchPathHistoryWitness T originalHole Q)
    (hclaw : G.IsClawFree)
    (hne : P ≠ Q) :
    ¬SharedDependentAnticommutingWitness
      A.block.path B.block.path
      A.block.dependentAt B.block.dependentAt := by
  intro hshared
  have hside : A.side = B.side :=
    A.side_eq_of_sharedDependentAnticommutingWitness B hshared
  rcases A with
    ⟨sideA, blockA, contextA, pathEqA, _outputA, _priorA, originalEqA⟩
  rcases B with
    ⟨sideB, blockB, contextB, pathEqB, _outputB, _priorB, originalEqB⟩
  cases sideA with
  | ac =>
      cases sideB with
      | ac =>
          have hOriginal :
              contextA.originalHole = contextB.originalHole :=
            originalEqA.trans originalEqB.symm
          have hpathNe :
              Set.range blockA.path.vertex ≠
                Set.range blockB.path.vertex := by
            intro hEq
            apply hne
            rw [← pathEqA, ← pathEqB]
            exact hEq
          exact
            (contextA.noSharedDependentAnticommutingWitness_of_same_oriented_history
              contextB hOriginal hclaw hpathNe) hshared
      | bd =>
          cases hside
  | bd =>
      cases sideB with
      | ac =>
          cases hside
      | bd =>
          have hOriginal :
              contextA.originalHole = contextB.originalHole :=
            originalEqA.trans originalEqB.symm
          have hpathNe :
              Set.range blockA.path.vertex ≠
                Set.range blockB.path.vertex := by
            intro hEq
            apply hne
            rw [← pathEqA, ← pathEqB]
            exact hEq
          exact
            (contextA.noSharedDependentAnticommutingWitness_of_same_oriented_history
              contextB hOriginal hclaw hpathNe) hshared

end TwoSidedSearchPathHistoryWitness

end FixedPairingPathFamily

end SimpleGraph
