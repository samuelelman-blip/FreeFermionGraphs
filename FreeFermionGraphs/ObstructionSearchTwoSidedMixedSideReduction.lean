import FreeFermionGraphs.ObstructionSearchTwoSidedMixedCommonNeighbor

/-!
# Mixed-side Corollary 11: component-side reduction

A vertex lying in Definition 20 dependent sets for an earlier block and the
current block lies in the prime colour opposite the introduced colour in each
block's local orientation.  The overlap-aware prime colouring therefore forces
the two blocks to use the same manuscript component side.

This is only the side-reduction step of Corollary 11.  It does not prove the
no-shared-witness conclusion, construct an obstruction-search execution, or
assume any conclusion of Lemma 14.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

private theorem dependent_mem_prime_of_mem_dependentAt
    (A : ConcretePathDeformation O Cprime)
    {s : Nat} {u : V}
    (hu : u ∈ A.dependentAt s) :
    u ∈ Cprime := by
  let i : Fin A.deformation.stepCount :=
    ⟨s, A.index_lt_of_mem_dependentAt hu⟩
  have huStep :
      u ∈ (A.deformation.step i).dependentSet := by
    simpa [i] using A.mem_step_dependentSet_of_mem_dependentAt hu
  exact
    ((ConcreteDeformationStep.mem_dependentSet
      (A.deformation.step i)).1 huStep).1

/-- Two side presentations whose common prime vertex lies in each oriented
`C'_d` class must use the same side.  The exclusion hypotheses are the exact
consequences supplied by the overlap-aware prime colourings. -/
private theorem side_eq_of_oriented_cd
    (sideA sideB : DeformationSide)
    {u : V}
    (huACd : u ∈ (sideA.family O).Cd)
    (huBCd : u ∈ (sideB.family O).Cd)
    (hnotA : u ∈ (sideA.family O).Cc →
      u ∉ (sideA.family O).Cd)
    (hnotB : u ∈ (sideB.family O).Cc →
      u ∉ (sideB.family O).Cd) :
    sideA = sideB := by
  cases sideA with
  | ac =>
      cases sideB with
      | ac => rfl
      | bd =>
          exfalso
          apply hnotA (by
            simpa [DeformationSide.family, swapSides] using huBCd)
          simpa [DeformationSide.family] using huACd
  | bd =>
      cases sideB with
      | ac =>
          exfalso
          apply hnotB (by
            simpa [DeformationSide.family, swapSides] using huACd)
          simpa [DeformationSide.family] using huBCd
      | bd => rfl

namespace MixedSideFullDefinition19Lemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}

/-- The opening reduction in the manuscript proof of Corollary 11 for one
positive mixed-side history: an earlier block and the current block sharing a
Definition 20 dependent vertex have equal component sides. -/
theorem priorSide_eq_currentSide_of_sharedDependentVertex
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    {r s t : Nat} {u : V}
    (huPrior : u ∈ (X.history.carrier.block r).dependentAt s)
    (huCurrent : u ∈ D.dependentAt t) :
    X.history.side r = X.currentSide := by
  have huPriorPrime : u ∈ Cprime :=
    dependent_mem_prime_of_mem_dependentAt
      (X.history.carrier.block r) huPrior
  have huCurrentPrime : u ∈ Cprime :=
    dependent_mem_prime_of_mem_dependentAt D huCurrent
  have huPriorOriented :
      u ∈ (X.history.orientedBlock r).dependentAt s := by
    rw [X.history.orientedBlock_dependentAt r s]
    exact huPrior
  have huCurrentOriented :
      u ∈ X.orientedCurrent.dependentAt t := by
    rw [X.orientedCurrent_dependentAt t]
    exact huCurrent
  have huPriorCd :
      u ∈ ((X.history.side r).family O).Cd :=
    (X.history.localData r).neighborhood.mechanical.dependent_mem_cd
      huPriorOriented
  have huCurrentCd :
      u ∈ (X.currentSide.family O).Cd :=
    X.current.neighborhood.mechanical.dependent_mem_cd huCurrentOriented
  have hnotPrior :
      u ∈ ((X.history.side r).family O).Cc →
        u ∉ ((X.history.side r).family O).Cd := by
    intro huCc
    exact
      ((X.history.localData r).neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
        huPriorPrime huCc).2
  have hnotCurrent :
      u ∈ (X.currentSide.family O).Cc →
        u ∉ (X.currentSide.family O).Cd := by
    intro huCc
    exact
      (X.current.neighborhood.overlapColoring.not_mem_ca_cd_of_mem_cc
        huCurrentPrime huCc).2
  exact side_eq_of_oriented_cd
    (X.history.side r) X.currentSide
    huPriorCd huCurrentCd hnotPrior hnotCurrent

/-- A shared dependent anticommuting witness between an earlier carrier block
and the current carrier block therefore compares two paths on the same
manuscript component side. -/
theorem priorSide_eq_currentSide_of_sharedDependentAnticommutingWitness
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (r : Nat)
    (hshared : SharedDependentAnticommutingWitness
      (X.history.carrier.block r).path D.path
      (X.history.carrier.block r).dependentAt D.dependentAt) :
    X.history.side r = X.currentSide := by
  rcases hshared with
    ⟨u, s, t, huPrior, huCurrent, _hantiPrior, _hantiCurrent⟩
  exact X.priorSide_eq_currentSide_of_sharedDependentVertex
    huPrior huCurrent

end MixedSideFullDefinition19Lemma11AHistoryData

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
