import FreeFermionGraphs.EvenHoleIndexedDeformation
import FreeFermionGraphs.Lemma11BAlternatingHoleCoordinates

/-!
# Lemma 11(b): a transported alternating-label sequence

This module packages the paper's alternating labels through the whole
one-path deformation.  Every before-hole uses one fixed half-length, each
successive labeling is the proved deformation of the preceding one, and
the removed `a`-coordinate advances by `next`.

These sequence invariants construct `AlternatingHoleCoordinates`; in
particular, the consecutive common-neighbor rule is now a theorem rather
than a separate hypothesis.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The alternating clone certificate at one concrete indexed step. -/
def stepCloneAt
    {k : Nat}
    (C : EvenHoleLabeling G k)
    (S : ConcreteDeformationStep O Cprime)
    (r : Fin k)
    (hcarrier : C.carrier = Set.range S.before.vertex)
    (hremoved : S.before.vertex S.removedIndex = C.a r) :
    C.CloneAt S.introduced r :=
  C.cloneAt_of_indexedDeformation
    S.before S.deformation r hcarrier hremoved

/-- A single alternating labeling transported through every concrete step,
with Definition 19's cyclic order on the removed `a`-indices. -/
structure AlternatingLabelingSequence
    (D : ConcretePathDeformation O Cprime) (k : Nat) where
  labeling :
    ∀ i : Fin D.deformation.stepCount,
      EvenHoleLabeling G k
  removedAIndex :
    ∀ i : Fin D.deformation.stepCount, Fin k
  carrier_eq :
    ∀ i : Fin D.deformation.stepCount,
      (labeling i).carrier =
        Set.range (D.deformation.step i).before.vertex
  removed_eq :
    ∀ i : Fin D.deformation.stepCount,
      (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex =
        (labeling i).a (removedAIndex i)
  transport :
    ∀ ⦃i j : Fin D.deformation.stepCount⦄,
      i.val + 1 = j.val →
      labeling j =
        (labeling i).deform
          (stepCloneAt
            (labeling i) (D.deformation.step i)
            (removedAIndex i) (carrier_eq i) (removed_eq i))
  removed_index_next :
    ∀ ⦃i j : Fin D.deformation.stepCount⦄,
      i.val + 1 = j.val →
      removedAIndex j =
        (labeling i).next (removedAIndex i)

namespace AlternatingLabelingSequence

variable {D : ConcretePathDeformation O Cprime} {k : Nat}

/-- The carrier of an alternating labeling has exactly twice its
half-length. -/
theorem EvenHoleLabeling.carrier_ncard
    (C : EvenHoleLabeling G k) :
    C.carrier.ncard = 2 * k := by
  have hdisjoint : Disjoint (Set.range C.a) (Set.range C.b) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨i, rfl⟩ ⟨j, hj⟩
    exact C.color_disjoint i j hj.symm
  rw [EvenHoleLabeling.carrier, Set.ncard_union_eq hdisjoint]
  simp [Set.ncard_range_of_injective C.a_injective,
    Set.ncard_range_of_injective C.b_injective]
  omega

/-- The alternating labeling at the first step already proves the paper's
initial hole is even; this is not a separate integration hypothesis. -/
theorem initialHole_even
    (A : D.AlternatingLabelingSequence k) :
    Even D.initialHole.card := by
  have hholeCard :
      (Set.range D.initialHole.vertex).ncard = D.initialHole.card := by
    simpa using
      Set.ncard_range_of_injective D.initialHole.injective
  have hcarrier :
      (A.labeling D.firstIndex).carrier =
        Set.range D.initialHole.vertex := by
    simpa [ConcretePathDeformation.initialHole] using
      A.carrier_eq D.firstIndex
  have hcard : D.initialHole.card = 2 * k := by
    calc
      D.initialHole.card =
          (Set.range D.initialHole.vertex).ncard := hholeCard.symm
      _ = (A.labeling D.firstIndex).carrier.ncard := by rw [hcarrier]
      _ = 2 * k :=
        EvenHoleLabeling.carrier_ncard (A.labeling D.firstIndex)
  rw [hcard]
  exact ⟨k, by omega⟩

/-- The indexed deformation supplies the alternating clone proof at every
step of the sequence. -/
def cloneAt
    (L : D.AlternatingLabelingSequence k)
    (i : Fin D.deformation.stepCount) :
    (L.labeling i).CloneAt
      (D.deformation.step i).introduced
      (L.removedAIndex i) :=
  stepCloneAt
    (L.labeling i) (D.deformation.step i)
    (L.removedAIndex i) (L.carrier_eq i) (L.removed_eq i)

/-- Normalized form of the sequence transport field. -/
theorem transport_eq
    (L : D.AlternatingLabelingSequence k)
    {i j : Fin D.deformation.stepCount}
    (hij : i.val + 1 = j.val) :
    L.labeling j =
      (L.labeling i).deform (L.cloneAt i) := by
  simpa [cloneAt] using L.transport hij

/-- A transported alternating-label sequence constructs the coordinate
package used by the consecutive-common-neighbor theorem. -/
def toAlternatingHoleCoordinates
    (L : D.AlternatingLabelingSequence k) :
    D.AlternatingHoleCoordinates where
  halfLength := fun _ => k
  labeling := L.labeling
  removedAIndex := L.removedAIndex
  carrier_eq := L.carrier_eq
  removed_eq := L.removed_eq
  next_removed_eq := by
    intro i j hij
    let hc := L.cloneAt i
    have htransport :
        (L.labeling j).a (L.removedAIndex j) =
          ((L.labeling i).deform hc).a
            (L.removedAIndex j) := by
      exact congrArg
        (fun C : EvenHoleLabeling G k =>
          C.a (L.removedAIndex j))
        (L.transport_eq hij)
    calc
      (D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex =
          (L.labeling j).a (L.removedAIndex j) :=
        L.removed_eq j
      _ = ((L.labeling i).deform hc).a
          (L.removedAIndex j) :=
        htransport
      _ = ((L.labeling i).deform hc).a
          ((L.labeling i).next (L.removedAIndex i)) := by
        rw [L.removed_index_next hij]
      _ = (L.labeling i).a
          ((L.labeling i).next (L.removedAIndex i)) := by
        exact (L.labeling i).deform_a_away hc
          ((L.labeling i).next_ne (L.removedAIndex i))

/-- The transported sequence discharges the raw consecutive-removed
common-neighbor rule. -/
theorem consecutiveRemovedCommonNeighborRule
    (L : D.AlternatingLabelingSequence k) :
    D.ConsecutiveRemovedCommonNeighborRule :=
  L.toAlternatingHoleCoordinates.consecutiveRemovedCommonNeighborRule

/-- Consequently the sequence supplies every complete paper
`w_(s-1)` certificate. -/
theorem consecutiveFourCommonNeighborRule
    (L : D.AlternatingLabelingSequence k)
    (M : D.MechanicalData) :
    ∀ ⦃i j : Fin D.deformation.stepCount⦄,
      i.val + 1 = j.val →
      D.HasConsecutiveFourCommonNeighbor i j :=
  L.toAlternatingHoleCoordinates.consecutiveFourCommonNeighborRule M

end AlternatingLabelingSequence

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
