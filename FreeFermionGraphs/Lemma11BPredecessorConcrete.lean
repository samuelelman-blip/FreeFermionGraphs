import FreeFermionGraphs.Lemma11BPredecessorLocal

/-!
# Lemma 11(b): concrete common-neighbor predecessors

A dependent vertex in an (a,c) deformation lies in the prime class paired
with C_b. The concrete mechanical geometry already proves this for every
dependent-set index. Therefore the local predecessor construction does not
need to repeat color-membership hypotheses for either the current or the
earlier vertex.

This module leaves exactly the local data drawn in the paper: a predecessor
one or two steps earlier and a shared neighbor in C_b.
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

/-- Every Nat-indexed dependent vertex belongs to the prime class C_d,
derived from its concrete step geometry. -/
theorem dependent_mem_cd
    (M : D.MechanicalData)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s) :
    u ∈ O.Cd := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huStep :
      u ∈ (D.deformation.step i).dependentSet := by
    simpa [i] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  exact (D.deformation.step i).dependent_mem_cd
    (M.stepGeometry i) huStep

end MechanicalData

/-- The concrete local predecessor construction after removing color
bookkeeping. -/
def OneOrTwoStepCommonBNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ D.dependentAt (Nat.succ s) →
    ¬D.path.AnticommutesWith u →
    ∃ s' : Nat, ∃ u' w : V,
      (s' = s ∨ Nat.succ s' = s) ∧
      u' ∈ D.dependentAt s' ∧
      w ∈ O.Cb ∧
      G.Adj u' w ∧
      G.Adj u w

/-- Mechanical color geometry upgrades the local common-neighbor rule to
the typed one-or-two-step predecessor rule. -/
theorem oneOrTwoStepCommonBPredecessorRule_of_commonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hlocal : D.OneOrTwoStepCommonBNeighborRule) :
    O.OneOrTwoStepCommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith := by
  intro s u hu hnotAnti
  obtain ⟨s', u', w, hstep, hu', hw, hu'w, huw⟩ :=
    hlocal hu hnotAnti
  refine ⟨s', u', w, hstep, hu', ?_, ?_, hw, hu'w, huw⟩
  · change u' ∈ O.Cd
    exact M.dependent_mem_cd hu'
  · change u ∈ O.Cd
    exact M.dependent_mem_cd hu

/-- The concrete base theorem and local shared-neighbor construction give
the full common-B predecessor rule with all color bookkeeping discharged. -/
theorem commonBPredecessorRule_of_localCommonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hbase : D.BaseStepData)
    (hlocal : D.OneOrTwoStepCommonBNeighborRule) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith := by
  apply D.commonBPredecessorRule_of_oneOrTwoStep hbase
  exact D.oneOrTwoStepCommonBPredecessorRule_of_commonNeighbors
    M hlocal

/-- Concrete Lemma 11(b) after discharging predecessor color memberships.
The remaining recursive input is only the local shared-C_b-neighbor
construction one or two steps earlier. -/
theorem lemma11b_of_ccTriples_and_localCommonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hEven : Even D.finalHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalTriple u)
    (hbase : D.BaseStepData)
    (hlocal : D.OneOrTwoStepCommonBNeighborRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_concretePathDeformation_of_ccIsolatedFinalTriples
    M hclaw hEven htriple
    (D.commonBPredecessorRule_of_localCommonNeighbors
      M hbase hlocal)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
