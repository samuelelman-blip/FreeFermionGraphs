import FreeFermionGraphs.Lemma11BColorTriple

/-!
# Lemma 11(b): base step of the concrete predecessor recursion

The predecessor recursion in Lemma 11(b) only has to construct a smaller
index at genuine successor steps. At step zero, a dependent vertex has the
initial active-path vertex as its unique path neighbor and therefore
anticommutes with the path.

This module formalizes that separation. It packages the concrete base-path
facts, proves base-step anticommutation, and upgrades a successor-only
common-neighbor rule to the full predecessor rule.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

/-- The recursive common-neighbor construction restricted to genuine
successor indices. -/
def SuccessorCommonBPredecessorRule
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (U : Nat → Set V) (Anticommutes : V → Prop) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u : V⦄,
    u ∈ U (Nat.succ s) →
    ¬Anticommutes u →
    ∃ s' : Nat, ∃ u' w : V,
      s' < Nat.succ s ∧
      u' ∈ U s' ∧
      u' ∈ σ.classFromB O.Cc O.Cd ∧
      u ∈ σ.classFromB O.Cc O.Cd ∧
      w ∈ O.Cb ∧
      G.Adj u' w ∧
      G.Adj u w

/-- A base anticommutation theorem and a successor-only construction give
the full common-neighbor predecessor rule. -/
theorem commonBPredecessorRule_of_base_and_successor
    (O : FixedPairingPathFamily G) (σ : PairingType)
    (U : Nat → Set V) (Anticommutes : V → Prop)
    (hbase : ∀ ⦃u : V⦄, u ∈ U 0 → Anticommutes u)
    (hsucc : O.SuccessorCommonBPredecessorRule σ U Anticommutes) :
    O.CommonBPredecessorRule σ U Anticommutes := by
  intro s u hu hnotAnti
  cases s with
  | zero =>
      exact (hnotAnti (hbase hu)).elim
  | succ s =>
      exact hsucc hu hnotAnti

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The two concrete path facts at the first deformation step. -/
structure BaseStepData
    (D : ConcretePathDeformation O Cprime) : Prop where
  startsAt :
    D.path.StartsAt
      (D.deformation.step D.firstIndex).introduced
  uniquePathNeighbor :
    ∀ ⦃u : V⦄,
      u ∈ D.dependentAt 0 →
      ∀ q : Fin D.path.card,
        G.Adj u (D.path.vertex q) →
        D.path.vertex q =
          (D.deformation.step D.firstIndex).introduced

/-- Every dependent vertex at the first step anticommutes with the active
path. -/
theorem baseDependentAnticommutes
    (D : ConcretePathDeformation O Cprime)
    (hbase : D.BaseStepData)
    {u : V} (hu : u ∈ D.dependentAt 0) :
    D.path.AnticommutesWith u := by
  have huStep :
      u ∈ (D.deformation.step D.firstIndex).dependentSet := by
    simpa [firstIndex] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  exact D.path.dependent_at_start_anticommutes
    huStep hbase.startsAt (hbase.uniquePathNeighbor hu)

/-- For a concrete path deformation, only successor steps need a local
predecessor construction. -/
theorem commonBPredecessorRule_of_successor
    (D : ConcretePathDeformation O Cprime)
    (hbase : D.BaseStepData)
    (hsucc :
      O.SuccessorCommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith := by
  exact O.commonBPredecessorRule_of_base_and_successor
    .ac D.dependentAt D.path.AnticommutesWith
    (fun {_u} hu => D.baseDependentAnticommutes hbase hu)
    hsucc

/-- Concrete Lemma 11(b) with the degree input reduced to the color-class
triple and the predecessor input reduced to successor steps. -/
theorem lemma11b_of_ccTriples_and_successorPredecessors
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
    (hsucc :
      O.SuccessorCommonBPredecessorRule
        .ac D.dependentAt D.path.AnticommutesWith)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_concretePathDeformation_of_ccIsolatedFinalTriples
    M hclaw hside hEven htriple
    (D.commonBPredecessorRule_of_successor hbase hsucc)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
