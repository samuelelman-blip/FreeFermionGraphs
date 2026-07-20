import FreeFermionGraphs.Lemma11BEvenness

/-!
# Lemma 11(b): predecessor attachments in Definition 20 form

The recursive branch of the paper identifies an earlier vertex by its
local relations to the introduced and removed vertices. Those are exactly
the four conditions defining `U⁽ʳ,ˢ⁾` in Definition 20.

This module proves the equivalence with `dependentAt` and reformulates
the remaining one/two-step attachment rule using only those raw graph
conditions. Membership in the earlier dependent set and all index
bookkeeping are then derived.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Definition 20's four local conditions at a Nat-indexed deformation
step, together with the fact that the step exists. -/
def Definition20DependentAt
    (D : ConcretePathDeformation O Cprime)
    (s : Nat) (u : V) : Prop :=
  ∃ hs : s < D.deformation.stepCount,
    u ∈ Cprime ∧
      G.Adj u (D.deformation.step ⟨s, hs⟩).introduced ∧
      u ≠
        (D.deformation.step ⟨s, hs⟩).before.vertex
          (D.deformation.step ⟨s, hs⟩).removedIndex ∧
      ¬G.Adj u
        ((D.deformation.step ⟨s, hs⟩).before.vertex
          (D.deformation.step ⟨s, hs⟩).removedIndex)

/-- The Nat-indexed dependent set is exactly Definition 20's raw local
adjacency and nonadjacency data. -/
theorem mem_dependentAt_iff_definition20
    (D : ConcretePathDeformation O Cprime)
    {s : Nat} {u : V} :
    u ∈ D.dependentAt s ↔ D.Definition20DependentAt s u := by
  constructor
  · intro hu
    have hs : s < D.deformation.stepCount :=
      D.index_lt_of_mem_dependentAt hu
    have huStep :
        u ∈ (D.deformation.step ⟨s, hs⟩).dependentSet :=
      D.mem_step_dependentSet_of_mem_dependentAt hu
    exact ⟨hs,
      (ConcreteDeformationStep.mem_dependentSet
        (D.deformation.step ⟨s, hs⟩)).1 huStep⟩
  · rintro ⟨hs, hraw⟩
    have huStep :
        u ∈ (D.deformation.step ⟨s, hs⟩).dependentSet :=
      (ConcreteDeformationStep.mem_dependentSet
        (D.deformation.step ⟨s, hs⟩)).2 hraw
    simpa [dependentAt, hs] using huStep

/-- The paper-level recursive input. An earlier vertex is specified by
Definition 20's raw conditions, either one step back or (when available)
two steps back, and by adjacency to the chosen `C_b` vertex. -/
def OneOrTwoStepDefinition20AttachmentRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃s : Nat⦄ ⦃u w : V⦄,
    u ∈ D.dependentAt (Nat.succ s) →
    ¬D.path.AnticommutesWith u →
    w ∈ O.Cb →
    G.Adj u w →
    (∃ u' : V,
      D.Definition20DependentAt s u' ∧
        G.Adj u' w) ∨
    (∃ t : Nat, Nat.succ t = s ∧
      ∃ u' : V,
        D.Definition20DependentAt t u' ∧
          G.Adj u' w)

/-- Raw Definition 20 attachment witnesses supply the abstract
one/two-step predecessor attachment rule. -/
theorem oneOrTwoStepPredecessorAlongBNeighborsRule_of_definition20
    (D : ConcretePathDeformation O Cprime)
    (hraw : D.OneOrTwoStepDefinition20AttachmentRule) :
    D.OneOrTwoStepPredecessorAlongBNeighborsRule := by
  intro s u w hu hnotAnti hw huw
  rcases hraw hu hnotAnti hw huw with
    hone | htwo
  · obtain ⟨u', hu', hu'w⟩ := hone
    exact ⟨s, u', Or.inl rfl,
      (D.mem_dependentAt_iff_definition20).2 hu', hu'w⟩
  · obtain ⟨t, hts, u', hu', hu'w⟩ := htwo
    exact ⟨t, u', Or.inr hts,
      (D.mem_dependentAt_iff_definition20).2 hu', hu'w⟩

/-- The reduced base parity input and raw Definition 20 attachment
construction give the full common-`C_b` predecessor rule. -/
theorem commonBPredecessorRule_of_definition20Attachments
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hraw : D.OneOrTwoStepDefinition20AttachmentRule) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith :=
  D.commonBPredecessorRule_of_baseParity_and_attachingPredecessors
    M hclaw horder hopposite
    (D.oneOrTwoStepPredecessorAlongBNeighborsRule_of_definition20 hraw)

/-- Concrete Lemma 11(b) with predecessor witnesses stated directly in
Definition 20 form and final evenness transported from the initial hole. -/
theorem lemma11b_of_initialEven_ccTriples_baseParity_and_definition20Attachments
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (hside : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s → O.PairingSideSeparated u)
    (hInitialEven : Even D.initialHole.card)
    (htriple : ∀ ⦃s : Nat⦄ ⦃u : V⦄,
      u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
      D.HasCCIsolatedFinalTriple u)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    (hraw : D.OneOrTwoStepDefinition20AttachmentRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_initialEven_ccTriples_baseParity_and_attachingPredecessors
    M hclaw hside hInitialEven htriple horder hopposite
    (D.oneOrTwoStepPredecessorAlongBNeighborsRule_of_definition20 hraw)
    hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
