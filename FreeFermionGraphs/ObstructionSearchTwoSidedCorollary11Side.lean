import FreeFermionGraphs.ObstructionSearchTwoSidedEarlierSelection

/-!
# Two-sided Corollary 11: component-side reduction

The proof of Corollary 11 first observes that a shared dependent vertex forces
the two compared path blocks to lie in the same component family.  For an
`ac` block, a dependent vertex lies in `C'_d`; for a `bd` block the side-swapped
statement places it in `C'_c`.  Since the two prime-hole colour classes are
disjoint, one vertex cannot be dependent on blocks of opposite sides.

This is the side-reduction step only.  The same-side no-shared-witness theorem
and the first-common-path argument remain separate.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace TwoSidedSearchPathHistoryWitness

/-- Every Definition 20 dependent vertex belongs to the fixed prime-hole
carrier. -/
theorem dependent_mem_prime
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    {s : Nat} {u : V}
    (hu : u ∈ A.block.dependentAt s) :
    u ∈ Cprime := by
  let i : Fin A.block.deformation.stepCount :=
    ⟨s, A.block.index_lt_of_mem_dependentAt hu⟩
  have huStep :
      u ∈ (A.block.deformation.step i).dependentSet := by
    simpa [i] using A.block.mem_step_dependentSet_of_mem_dependentAt hu
  exact
    ((ConcreteDeformationStep.mem_dependentSet
      (A.block.deformation.step i)).1 huStep).1

/-- In the family oriented by the recorded side, a dependent vertex lies in
the prime class opposite the introduced class. -/
theorem dependent_mem_oriented_cd
    {S : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    {s : Nat} {u : V}
    (hu : u ∈ A.block.dependentAt s) :
    u ∈ (A.side.family O).Cd :=
  A.context.currentData.neighborhood.mechanical.dependent_mem_cd hu

/-- The first reduction in the manuscript proof of Corollary 11: two path
blocks sharing a Definition 20 dependent vertex have the same component side.

For opposite sides, the shared vertex would lie in both `C'_c` and `C'_d`.
The contradiction uses the overlap-aware prime-hole colouring, so no global
`ExactlyOneOfFour` assumption is introduced. -/
theorem side_eq_of_sharedDependentVertex
    {S T : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P Q : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    (B : TwoSidedSearchPathHistoryWitness T originalHole Q)
    {u : V} {s t : Nat}
    (huA : u ∈ A.block.dependentAt s)
    (huB : u ∈ B.block.dependentAt t) :
    A.side = B.side := by
  have huAPrime : u ∈ Cprime := A.dependent_mem_prime huA
  have huBPrime : u ∈ Cprime := B.dependent_mem_prime huB
  have huAOrientedCd : u ∈ (A.side.family O).Cd :=
    A.dependent_mem_oriented_cd huA
  have huBOrientedCd : u ∈ (B.side.family O).Cd :=
    B.dependent_mem_oriented_cd huB
  cases hA : A.side with
  | ac =>
      cases hB : B.side with
      | ac =>
          simpa [hA, hB]
      | bd =>
          exfalso
          have huCd : u ∈ O.Cd := by
            simpa [hA, DeformationSide.family] using huAOrientedCd
          have huCc : u ∈ O.Cc := by
            simpa [hB, DeformationSide.family, swapSides] using
              huBOrientedCd
          have huNotCd : u ∉ O.Cd :=
            (A.context.currentData.neighborhood.overlapColoring
              .not_mem_ca_cd_of_mem_cc huAPrime huCc).2
          exact huNotCd huCd
  | bd =>
      cases hB : B.side with
      | ac =>
          exfalso
          have huCc : u ∈ O.Cc := by
            simpa [hA, DeformationSide.family, swapSides] using
              huAOrientedCd
          have huCd : u ∈ O.Cd := by
            simpa [hB, DeformationSide.family] using huBOrientedCd
          have huNotCd : u ∉ O.Cd :=
            (B.context.currentData.neighborhood.overlapColoring
              .not_mem_ca_cd_of_mem_cc huBPrime huCc).2
          exact huNotCd huCd
      | bd =>
          simpa [hA, hB]

/-- A shared dependent anticommuting witness therefore compares two blocks on
the same manuscript component side. -/
theorem side_eq_of_sharedDependentAnticommutingWitness
    {S T : SearchDeformation O Cprime}
    {originalHole : IndexedInducedHole G}
    {P Q : Set V}
    (A : TwoSidedSearchPathHistoryWitness S originalHole P)
    (B : TwoSidedSearchPathHistoryWitness T originalHole Q)
    (hshared : SharedDependentAnticommutingWitness
      A.block.path B.block.path
      A.block.dependentAt B.block.dependentAt) :
    A.side = B.side := by
  rcases hshared with ⟨u, s, t, huA, huB, _hantiA, _hantiB⟩
  exact A.side_eq_of_sharedDependentVertex B huA huB

end TwoSidedSearchPathHistoryWitness

end FixedPairingPathFamily

end SimpleGraph
