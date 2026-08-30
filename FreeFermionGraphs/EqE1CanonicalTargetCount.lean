import FreeFermionGraphs.EqE1ClassWeightData

/-!
# The finite target-count boundary in Eq. (E1)

For the uniform normalization, deformation compatibility is exactly a finite
cardinality question.  This module states that question without any scalar,
operator, amplitude, or matrix-power data and proves that it supplies the
remaining normalization law for the canonical class-native Eq. (E1) record.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- Pure graph form of the remaining canonical-normalization condition. -/
def CanonicalBubbleWandTargetCountInvariant
    (G : SimpleGraph V) (K : Set V) [Fintype V] : Prop :=
  ∀ (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val),
    EvenHoopBubbleWandArc G K
      (P.initialSegment r) (P.initialSegment s) →
      (bubbleWandTargetsInClass G K (P.initialSegment r)
          (canonicalBubbleWandArcClass G K
            (P.initialSegment r) (P.initialSegment s))).card =
        (bubbleWandTargetsInClass G K (P.deformedPrefix h r)
          (canonicalBubbleWandArcClass G K
            (P.deformedPrefix h r) (P.deformedPrefix h s))).card

namespace EqE1ClassWeightData

variable {G : SimpleGraph V} {K : Set V} {R : Type w}

/-- Equality of the explicit finite target counts gives equality of the
uniform class normalizations over every field. -/
theorem canonical_hasDeformationCompatibleNormalization_of_targetCount
    [Fintype V] [Field R]
    (hcount : CanonicalBubbleWandTargetCountInvariant G K)
    (coupling : V → R)
    (generalizedCycleEigenvalue : EvenHoleDeformationClass G → R) :
    (canonicalEqE1ClassWeightData G K R coupling
      generalizedCycleEigenvalue).HasDeformationCompatibleNormalization := by
  intro P k j i h hj r s hir his harc
  unfold canonicalBubbleWandClassNormalization
  change
    ((bubbleWandTargetsInClass G K (P.initialSegment r)
        (canonicalBubbleWandArcClass G K
          (P.initialSegment r) (P.initialSegment s))).card : R) / 2 =
      ((bubbleWandTargetsInClass G K (P.deformedPrefix h r)
        (canonicalBubbleWandArcClass G K
          (P.deformedPrefix h r) (P.deformedPrefix h s))).card : R) / 2
  rw [hcount P h hj r s hir his harc]

/-- Under the two remaining pure graph conditions, the canonical class-native
Eq. (E1) data satisfies the complete local weight compatibility interface. -/
theorem canonical_toEqE1WeightData_isDeformationCompatible
    [Fintype V] [Field R]
    (hclaw : G.IsClawFree)
    (hunique : BubbleWandEventClassUnique G K)
    (hcount : CanonicalBubbleWandTargetCountInvariant G K)
    (coupling : V → R)
    (generalizedCycleEigenvalue : EvenHoleDeformationClass G → R) :
    (canonicalEqE1ClassWeightData G K R coupling
      generalizedCycleEigenvalue).toEqE1WeightData.IsDeformationCompatible := by
  let W := canonicalEqE1ClassWeightData G K R coupling
    generalizedCycleEigenvalue
  apply W.toEqE1WeightData_isDeformationCompatible hclaw
  · exact canonicalEqE1ClassWeightData_isEventFaithful
      hunique coupling generalizedCycleEigenvalue
  · exact canonical_hasDeformationCompatibleNormalization_of_targetCount
      hcount coupling generalizedCycleEigenvalue

end EqE1ClassWeightData

/-- Complete local Eq. (E1) prefix-entry invariance for the canonical
quotient-indexed data, reduced only to the two scalar-free graph conditions. -/
theorem RootedInducedPath.canonical_eqE1_deformedPrefix_weight
    {G : SimpleGraph V} {K : Set V} {R : Type w}
    [Fintype V] [Field R]
    (hK : G.IsClique K) (hclaw : G.IsClawFree)
    (hunique : BubbleWandEventClassUnique G K)
    (hcount : CanonicalBubbleWandTargetCountInvariant G K)
    (coupling : V → R)
    (generalizedCycleEigenvalue : EvenHoleDeformationClass G → R)
    (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val) :
    let W := (canonicalEqE1ClassWeightData G K R coupling
      generalizedCycleEigenvalue).toEqE1WeightData
    eqE1WeightedAdjacency G K W
        (P.initialSegment r) (P.initialSegment s) =
      eqE1WeightedAdjacency G K W
        (P.deformedPrefix h r) (P.deformedPrefix h s) := by
  dsimp only
  let W := (canonicalEqE1ClassWeightData G K R coupling
    generalizedCycleEigenvalue).toEqE1WeightData
  have hW : W.IsDeformationCompatible :=
    EqE1ClassWeightData.canonical_toEqE1WeightData_isDeformationCompatible
      hclaw hunique hcount coupling generalizedCycleEigenvalue
  exact RootedInducedPath.eqE1_deformedPrefix_weight
    hK hclaw W hW P h hj r s hir his

end SimpleGraph
