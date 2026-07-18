import FreeFermionGraphs.Lemma11BBaseParity

/-!
# Lemma 11(b): transporting evenness through the deformation

The paper starts with an even hole. Every single-vertex deformation keeps
the same cyclic index type, and consecutive concrete steps have the same
intermediate carrier. Hence every hole in a concrete path deformation has
the same cardinality.

This module derives evenness of the final hole from evenness of the initial
hole, removing a duplicated final-hole assumption from the concrete
Lemma 11(b) theorem.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- Indexed holes with equal carriers have equal cardinalities. -/
theorem card_eq_of_range_eq
    (C D : IndexedInducedHole G)
    (hcarrier : Set.range C.vertex = Set.range D.vertex) :
    C.card = D.card := by
  have hC : (Set.range C.vertex).ncard = C.card := by
    simpa using Set.ncard_range_of_injective C.injective
  have hD : (Set.range D.vertex).ncard = D.card := by
    simpa using Set.ncard_range_of_injective D.injective
  calc
    C.card = (Set.range C.vertex).ncard := hC.symm
    _ = (Set.range D.vertex).ncard :=
      congrArg Set.ncard hcarrier
    _ = D.card := hD

end IndexedInducedHole

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcreteDeformationStep

/-- A concrete deformation step preserves the hole cardinality. -/
@[simp]
theorem after_card
    (S : ConcreteDeformationStep O Cprime) :
    S.after.card = S.before.card := by
  simp [after]

end ConcreteDeformationStep

namespace ConcreteDeformation

/-- Every before-hole in a nonempty concrete deformation has the same
cardinality as the first before-hole. -/
theorem before_card_eq_first
    (D : ConcreteDeformation O Cprime)
    (hpos : 0 < D.stepCount)
    (s : Nat) (hs : s < D.stepCount) :
    (D.step ⟨s, hs⟩).before.card =
      (D.step ⟨0, hpos⟩).before.card := by
  induction s with
  | zero =>
      rfl
  | succ s ih =>
      have hsPrev : s < D.stepCount := by
        omega
      let i : Fin D.stepCount := ⟨s, hsPrev⟩
      let j : Fin D.stepCount := ⟨Nat.succ s, hs⟩
      have hcarrier :
          Set.range (D.step i).after.vertex =
            Set.range (D.step j).before.vertex := by
        apply D.carrier_chain
        rfl
      have hcard :
          (D.step i).after.card =
            (D.step j).before.card :=
        IndexedInducedHole.card_eq_of_range_eq
          (D.step i).after (D.step j).before hcarrier
      change
        (D.step j).before.card =
          (D.step ⟨0, hpos⟩).before.card
      calc
        (D.step j).before.card =
            (D.step i).after.card := hcard.symm
        _ = (D.step i).before.card := by
          simp
        _ = (D.step ⟨0, hpos⟩).before.card := by
          simpa [i] using ih hsPrev

end ConcreteDeformation

namespace ConcretePathDeformation

/-- The final and initial holes of a nonempty path deformation have the
same cardinality. -/
theorem finalHole_card_eq_initialHole_card
    (D : ConcretePathDeformation O Cprime) :
    D.finalHole.card = D.initialHole.card := by
  have hlast :
      D.deformation.stepCount - 1 <
        D.deformation.stepCount := by
    have hpos : 0 < D.deformation.stepCount := D.nonempty
    omega
  have hbefore :
      (D.deformation.step D.lastIndex).before.card =
        (D.deformation.step D.firstIndex).before.card := by
    simpa [lastIndex, firstIndex] using
      D.deformation.before_card_eq_first
        D.nonempty (D.deformation.stepCount - 1) hlast
  calc
    D.finalHole.card =
        (D.deformation.step D.lastIndex).before.card := by
      simp [finalHole]
    _ = (D.deformation.step D.firstIndex).before.card := hbefore
    _ = D.initialHole.card := rfl

/-- Evenness of the original hole is inherited by the final deformed
hole. -/
theorem finalHole_even_of_initialHole_even
    (D : ConcretePathDeformation O Cprime)
    (hEven : Even D.initialHole.card) :
    Even D.finalHole.card := by
  rw [D.finalHole_card_eq_initialHole_card]
  exact hEven

/-- Concrete Lemma 11(b) with final-hole evenness derived from the initial
hole's evenness. -/
theorem lemma11b_of_initialEven_ccTriples_baseParity_and_attachingPredecessors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalTriple u)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hattach : D.OneOrTwoStepPredecessorAlongBNeighborsRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_ccTriples_baseParity_and_attachingPredecessors
    M hclaw
    (D.finalHole_even_of_initialHole_even hInitialEven)
    htriple horder hopposite hattach hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
