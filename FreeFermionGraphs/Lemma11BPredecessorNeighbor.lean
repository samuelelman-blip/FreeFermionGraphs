import FreeFermionGraphs.Lemma11BPredecessorConcrete

/-!
# Lemma 11(b): deriving the current C_b neighbor

The single-deformation common-neighbor theorem already gives every
dependent vertex a neighbor in C_b. The paper's recursive case analysis
then finds an earlier dependent vertex adjacent to that same neighbor.

This module separates those tasks. The mechanical data supplies the current
C_b neighbor; the remaining local rule only attaches an earlier dependent
vertex one or two steps back.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace MechanicalData

variable {D : ConcretePathDeformation O Cprime}

/-- Every concrete dependent vertex has a C_b neighbor, obtained from the
persistent common-hole neighbor at its deformation step. -/
theorem exists_b_neighbor
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    ∃ w : V, w ∈ O.Cb ∧ G.Adj u w := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huStep :
      u ∈ (D.deformation.step i).dependentSet := by
    simpa [i] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  obtain ⟨w, _hwBefore, huw, _hintroducedw,
      _hremovedw, hwCb⟩ :=
    (D.deformation.step i).dependent_commonNeighbor_mem_cb
      (M.stepGeometry i) hclaw huStep
      (M.outsideHole i huStep)
  exact ⟨w, hwCb, huw⟩

end MechanicalData

/-- The remaining local recursive task: every C_b neighbor of the current
commuting dependent vertex also neighbors a dependent vertex one or two
steps earlier. -/
def OneOrTwoStepPredecessorAlongBNeighborsRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u w : V⦄,
    u ∈ D.dependentAt (Nat.succ s) →
    ¬D.path.AnticommutesWith u →
    w ∈ O.Cb →
    G.Adj u w →
    ∃ s' : Nat, ∃ u' : V,
      (s' = s ∨ Nat.succ s' = s) ∧
      u' ∈ D.dependentAt s' ∧
      G.Adj u' w

/-- The mechanically supplied current neighbor and the attachment rule give
the local shared-C_b-neighbor construction. -/
theorem oneOrTwoStepCommonBNeighborRule_of_attachingPredecessors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hattach : D.OneOrTwoStepPredecessorAlongBNeighborsRule) :
    D.OneOrTwoStepCommonBNeighborRule := by
  intro s u hu hnotAnti
  obtain ⟨w, hw, huw⟩ := M.exists_b_neighbor hclaw hu
  obtain ⟨s', u', hstep, hu', hu'w⟩ :=
    hattach hu hnotAnti hw huw
  exact ⟨s', u', w, hstep, hu', hw, hu'w, huw⟩

/-- The base theorem and local attachment rule give the full predecessor
rule, with the current C_b neighbor derived mechanically. -/
theorem commonBPredecessorRule_of_attachingPredecessors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hbase : D.BaseStepData)
    (hattach : D.OneOrTwoStepPredecessorAlongBNeighborsRule) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith := by
  apply D.commonBPredecessorRule_of_localCommonNeighbors
    M hbase
  exact D.oneOrTwoStepCommonBNeighborRule_of_attachingPredecessors
    M hclaw hattach

/-- Concrete Lemma 11(b) after deriving the current shared C_b neighbor.
The remaining predecessor case only attaches an earlier dependent vertex
to that neighbor. -/
theorem lemma11b_of_ccTriples_and_attachingPredecessors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hside : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s → O.PairingSideSeparated u)
    (hEven : Even D.finalHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalTriple u)
    (hbase : D.BaseStepData)
    (hattach : D.OneOrTwoStepPredecessorAlongBNeighborsRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_concretePathDeformation_of_ccIsolatedFinalTriples
    M hclaw hside hEven htriple
    (D.commonBPredecessorRule_of_attachingPredecessors
      M hclaw hbase hattach)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
