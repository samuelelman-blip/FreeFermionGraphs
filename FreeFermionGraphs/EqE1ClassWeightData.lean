import FreeFermionGraphs.CanonicalBubbleWandClassNormalization
import FreeFermionGraphs.InducedPathDeformationBubbleWandEvent
import FreeFermionGraphs.InducedPathDeformationLocalWeights

/-!
# Class-native Eq. (E1) weight data

The printed generalized-cycle coefficient is indexed by `⟨C₀⟩`.  This module
stores that quotient class directly, converts it to the legacy carrier-based
Eq. (E1) interface without changing the coefficient, and derives deformation
compatibility from retained bubble-wand events.

The only residual condition is graph-theoretic: if the Boolean directed graph
collapses several concrete events into one source-target arc, those events
must name the same even-hole deformation class.
-/

universe u w

variable {V : Type u}

namespace SimpleGraph

/-- Eq. (E1) scalar data with generalized cycles indexed by the genuine
deformation quotient. -/
structure EqE1ClassWeightData
    (G : SimpleGraph V) (K : Set V) (R : Type w) where
  coupling : V → R
  bubbleClass :
    CliqueRootedInducedPath G K → CliqueRootedInducedPath G K →
      EvenHoleDeformationClass G
  generalizedCycleEigenvalue : EvenHoleDeformationClass G → R

namespace EqE1ClassWeightData

variable {G : SimpleGraph V} {K : Set V} {R : Type w}

/-- Interpret class-native data in the original carrier-valued Eq. (E1)
record.  `Quotient.out` is used only to satisfy that legacy field; both the
eigenvalue and normalization immediately map it back to its quotient class. -/
noncomputable def toEqE1WeightData
    [Fintype V] [Field R]
    (W : EqE1ClassWeightData G K R) : EqE1WeightData G K R where
  coupling := W.coupling
  bubbleClosure P Q := Quotient.out (W.bubbleClass P Q)
  generalizedCycleEigenvalue C :=
    W.generalizedCycleEigenvalue (G.evenHoleDeformationClassOf C)
  normalization P Q C :=
    canonicalBubbleWandClassNormalization G K P Q
      (G.evenHoleDeformationClassOf C)

@[simp]
theorem toEqE1WeightData_bubbleClosure_class
    [Fintype V] [Field R]
    (W : EqE1ClassWeightData G K R)
    (P Q : CliqueRootedInducedPath G K) :
    G.evenHoleDeformationClassOf
        ((W.toEqE1WeightData).bubbleClosure P Q) =
      W.bubbleClass P Q := by
  exact Quotient.out_eq _

/-- The legacy conversion computes exactly the quotient-indexed coefficient,
with no dependence on the representative chosen by `Quotient.out`. -/
theorem toEqE1WeightData_bubbleWeight
    [Fintype V] [Field R]
    (W : EqE1ClassWeightData G K R)
    (P Q : CliqueRootedInducedPath G K) :
    (W.toEqE1WeightData).bubbleWeight P Q =
      W.generalizedCycleEigenvalue (W.bubbleClass P Q) /
        canonicalBubbleWandClassNormalization G K P Q
          (W.bubbleClass P Q) := by
  unfold EqE1WeightData.bubbleWeight
  change
    W.generalizedCycleEigenvalue
          (G.evenHoleDeformationClassOf
            ((W.toEqE1WeightData).bubbleClosure P Q)) /
        canonicalBubbleWandClassNormalization G K P Q
          (G.evenHoleDeformationClassOf
            ((W.toEqE1WeightData).bubbleClosure P Q)) = _
  rw [W.toEqE1WeightData_bubbleClosure_class]

/-- A class assignment is faithful to the event-level relation when every
retained event on an arc has exactly the assigned quotient class. -/
def IsEventFaithful
    (W : EqE1ClassWeightData G K R) : Prop :=
  ∀ (P Q : CliqueRootedInducedPath G K) (bubble : V),
    EvenHoopBubbleWandEvent G K P Q bubble →
      W.bubbleClass P Q =
        G.evenHoleDeformationClassOf
          (bubbleWandArcHoopCarrier P Q bubble)

/-- Event faithfulness and the concrete event transport force the assigned
class itself to be invariant under a handle deformation. -/
theorem bubbleClass_deformedPrefix_eq
    (W : EqE1ClassWeightData G K R)
    (hclaw : G.IsClawFree) (hfaithful : W.IsEventFaithful)
    (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val)
    (harc : EvenHoopBubbleWandArc G K
      (P.initialSegment r) (P.initialSegment s)) :
    W.bubbleClass (P.initialSegment r) (P.initialSegment s) =
      W.bubbleClass (P.deformedPrefix h r) (P.deformedPrefix h s) := by
  obtain ⟨bubble, ⟨E⟩⟩ :=
    evenHoopBubbleWandArc_iff_exists_event.mp harc
  let E' := P.evenHoopBubbleWandEvent_deformedPrefix
    hclaw h hj r s hir his E
  calc
    W.bubbleClass (P.initialSegment r) (P.initialSegment s) =
        G.evenHoleDeformationClassOf
          (bubbleWandArcHoopCarrier
            (P.initialSegment r) (P.initialSegment s) bubble) :=
      hfaithful _ _ bubble E
    _ = G.evenHoleDeformationClassOf
          (bubbleWandArcHoopCarrier
            (P.deformedPrefix h r) (P.deformedPrefix h s) bubble) :=
      P.bubbleWandArcHoopClass_deformedPrefix_eq
        hclaw h hj r s hir his E
    _ = W.bubbleClass
          (P.deformedPrefix h r) (P.deformedPrefix h s) :=
      (hfaithful _ _ bubble E').symm

/-- The remaining normalization condition after quotient classes and their
eigenvalues have been made canonical.  It is an equality of two explicit
finite target counts, not an amplitude or matrix-power hypothesis. -/
def HasDeformationCompatibleNormalization
    [Fintype V] [Field R]
    (W : EqE1ClassWeightData G K R) : Prop :=
  ∀ (P : CliqueRootedInducedPath G K) {k j : V}
    {i : Fin P.path.card}
    (h : P.path.SingleVertexDeformation (some k) i)
    (hj : P.path.vertex i = some j)
    (r s : Fin P.path.card) (hir : i.val ≤ r.val) (his : i.val ≤ s.val),
    EvenHoopBubbleWandArc G K
      (P.initialSegment r) (P.initialSegment s) →
      (canonicalBubbleWandClassNormalization G K
          (P.initialSegment r) (P.initialSegment s)
          (W.bubbleClass (P.initialSegment r) (P.initialSegment s)) : R) =
        (canonicalBubbleWandClassNormalization G K
          (P.deformedPrefix h r) (P.deformedPrefix h s)
          (W.bubbleClass
            (P.deformedPrefix h r) (P.deformedPrefix h s)) : R)

/-- For class-native data, event faithfulness derives the full local
generalized-cycle coefficient law used by the existing Eq. (E1) theorem. -/
theorem toEqE1WeightData_isDeformationCompatible
    [Fintype V] [Field R]
    (W : EqE1ClassWeightData G K R)
    (hclaw : G.IsClawFree) (hfaithful : W.IsEventFaithful)
    (hnormal : W.HasDeformationCompatibleNormalization) :
    W.toEqE1WeightData.IsDeformationCompatible := by
  refine { bubbleWeight_eq := ?_ }
  intro P k j i h hj r s hir his harc
  rw [W.toEqE1WeightData_bubbleWeight]
  rw [W.toEqE1WeightData_bubbleWeight]
  have hclass := W.bubbleClass_deformedPrefix_eq
    hclaw hfaithful P h hj r s hir his harc
  have hnormal' := hnormal P h hj r s hir his harc
  rw [hclass] at hnormal'
  rw [hclass, hnormal']

end EqE1ClassWeightData

/-- The exact remaining well-definedness condition created by representing
the event relation as a Boolean source-target arc relation. -/
def BubbleWandEventClassUnique
    (G : SimpleGraph V) (K : Set V) : Prop :=
  ∀ (P Q : CliqueRootedInducedPath G K) (bubble bubble' : V)
    (E : EvenHoopBubbleWandEvent G K P Q bubble)
    (E' : EvenHoopBubbleWandEvent G K P Q bubble'),
      G.evenHoleDeformationClassOf
          (bubbleWandArcHoopCarrier P Q bubble) =
        G.evenHoleDeformationClassOf
          (bubbleWandArcHoopCarrier P Q bubble')

/-- Select the quotient class of an actual event on a Boolean arc.  Away from
event arcs the value is irrelevant to Eq. (E1), so the empty carrier class is
used as a total default. -/
noncomputable def canonicalBubbleWandArcClass
    (G : SimpleGraph V) (K : Set V)
    (P Q : CliqueRootedInducedPath G K) :
    EvenHoleDeformationClass G := by
  classical
  exact
    if h : ∃ bubble : V,
        Nonempty (EvenHoopBubbleWandEvent G K P Q bubble) then
      let bubble := Classical.choose h
      let E := Classical.choice (Classical.choose_spec h)
      G.evenHoleDeformationClassOf
        (bubbleWandArcHoopCarrier P Q bubble)
    else
      G.evenHoleDeformationClassOf ∅

/-- Class uniqueness makes the canonical event selection faithful to every
event represented by the same Boolean arc. -/
theorem canonicalBubbleWandArcClass_eq_of_event
    {G : SimpleGraph V} {K : Set V}
    (hunique : BubbleWandEventClassUnique G K)
    (P Q : CliqueRootedInducedPath G K) (bubble : V)
    (E : EvenHoopBubbleWandEvent G K P Q bubble) :
    canonicalBubbleWandArcClass G K P Q =
      G.evenHoleDeformationClassOf
        (bubbleWandArcHoopCarrier P Q bubble) := by
  classical
  unfold canonicalBubbleWandArcClass
  let hExists : ∃ bubble : V,
      Nonempty (EvenHoopBubbleWandEvent G K P Q bubble) :=
    ⟨bubble, ⟨E⟩⟩
  rw [dif_pos hExists]
  exact hunique P Q (Classical.choose hExists) bubble
    (Classical.choice (Classical.choose_spec hExists)) E

/-- The canonical class-native Eq. (E1) data. -/
noncomputable def canonicalEqE1ClassWeightData
    (G : SimpleGraph V) (K : Set V) (R : Type w)
    (coupling : V → R)
    (generalizedCycleEigenvalue : EvenHoleDeformationClass G → R) :
    EqE1ClassWeightData G K R where
  coupling := coupling
  bubbleClass := canonicalBubbleWandArcClass G K
  generalizedCycleEigenvalue := generalizedCycleEigenvalue

/-- The canonical quotient assignment is event-faithful under precisely the
Boolean-arc class-uniqueness condition. -/
theorem canonicalEqE1ClassWeightData_isEventFaithful
    {G : SimpleGraph V} {K : Set V} {R : Type w}
    (hunique : BubbleWandEventClassUnique G K)
    (coupling : V → R)
    (generalizedCycleEigenvalue : EvenHoleDeformationClass G → R) :
    (canonicalEqE1ClassWeightData G K R coupling
      generalizedCycleEigenvalue).IsEventFaithful := by
  intro P Q bubble E
  exact canonicalBubbleWandArcClass_eq_of_event
    hunique P Q bubble E

end SimpleGraph
