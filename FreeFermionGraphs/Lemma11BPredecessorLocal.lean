import FreeFermionGraphs.Lemma11BPredecessorBase

/-!
# Lemma 11(b): one- or two-step predecessor construction

The recursive local argument in Lemma 11(b) replaces a commuting dependent
vertex by a vertex in a dependent set one or two steps earlier. This is the
paper's choice of delta in the set {1, 2}.

This module states that bounded local rule and proves that it supplies the
successor predecessor rule, hence the full well-founded predecessor rule
once the base step has been discharged.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- A common-neighbor predecessor is found exactly one or two steps before
the current successor index. For current index succ s, the predecessor
index is either s or the predecessor of s. -/
def OneOrTwoStepCommonBPredecessorRule
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (U : Nat → Set V) (Anticommutes : V → Prop) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U (Nat.succ s) →
    ¬Anticommutes u →
    ∃ s' : Nat, ∃ u' w : V,
      (s' = s ∨ Nat.succ s' = s) ∧
      u' ∈ U s' ∧
      u' ∈ σ.classFromB O.Cc O.Cd ∧
      u ∈ σ.classFromB O.Cc O.Cd ∧
      w ∈ O.Cb ∧
      G.Adj u' w ∧
      G.Adj u w

/-- A one- or two-step local construction is a successor predecessor rule. -/
theorem successorCommonBPredecessorRule_of_oneOrTwoStep
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (hlocal : O.OneOrTwoStepCommonBPredecessorRule
      σ U Anticommutes) :
    O.SuccessorCommonBPredecessorRule σ U Anticommutes := by
  intro s u hu hnotAnti
  obtain ⟨s', u', w, hstep, hu', hu'Class, huClass,
    hw, hu'w, huw⟩ := hlocal hu hnotAnti
  refine ⟨s', u', w, ?_, hu', hu'Class, huClass,
    hw, hu'w, huw⟩
  rcases hstep with hs | hs
  · omega
  · omega

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- For a concrete path deformation, the base theorem and the paper's
one-or-two-step construction give the full predecessor rule. -/
theorem commonBPredecessorRule_of_oneOrTwoStep
    (D : ConcretePathDeformation O Cprime)
    (hbase : D.BaseStepData)
    (hlocal :
      O.OneOrTwoStepCommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith := by
  apply D.commonBPredecessorRule_of_successor hbase
  exact O.successorCommonBPredecessorRule_of_oneOrTwoStep
    .ac D.dependentAt D.path.AnticommutesWith hlocal

/-- Concrete Lemma 11(b) with both remaining local inputs in the forms used
by the paper: a color-class neighbor triple and a one-or-two-step common
neighbor predecessor. -/
theorem lemma11b_of_ccTriples_and_oneOrTwoStepPredecessors
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
    (hlocal :
      O.OneOrTwoStepCommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_concretePathDeformation_of_ccIsolatedFinalTriples
    M hclaw hside hEven htriple
    (D.commonBPredecessorRule_of_oneOrTwoStep hbase hlocal)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
