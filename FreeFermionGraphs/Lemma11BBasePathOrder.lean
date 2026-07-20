import FreeFermionGraphs.Lemma11BPredecessorNeighbor

/-!
# Lemma 11(b): the ordered base path

Definition 19 labels the active path as
`j₀-k₀-j₁-k₁-...`.  Thus, at deformation index `s`, the
introduced vertex has path index `2s` and the removed vertex has path
index `2s+1`.

At the first deformation step this makes the introduced vertex the initial
endpoint automatically.  Consequently the base case no longer needs a
packaged `BaseStepData`: only the genuinely local statement that a
first-step dependent vertex has no other path neighbor remains.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The path-index arithmetic in Definition 19's labeling. -/
structure Definition19PathOrder
    {D : ConcretePathDeformation O Cprime}
    (M : D.MechanicalData) : Prop where
  introduced_index_val :
    ∀ i : Fin D.deformation.stepCount,
      (M.stepLabeling i).introducedPathIndex.val = 2 * i.val
  removed_index_val :
    ∀ i : Fin D.deformation.stepCount,
      (M.stepLabeling i).removedPathIndex.val = 2 * i.val + 1

namespace MechanicalData

variable {D : ConcretePathDeformation O Cprime}

/-- The first introduced vertex is at path index zero. -/
theorem firstIntroducedIndex_val_eq_zero
    (M : D.MechanicalData)
    (horder : Definition19PathOrder M) :
    (M.stepLabeling D.firstIndex).introducedPathIndex.val = 0 := by
  simpa [firstIndex] using
    horder.introduced_index_val D.firstIndex

/-- The first removed vertex is the next path vertex, at index one. -/
theorem firstRemovedIndex_val_eq_one
    (M : D.MechanicalData)
    (horder : Definition19PathOrder M) :
    (M.stepLabeling D.firstIndex).removedPathIndex.val = 1 := by
  simpa [firstIndex] using
    horder.removed_index_val D.firstIndex

/-- Definition 19's path order proves the `startsAt` field of the base
step data. -/
theorem startsAt_firstIntroduced
    (M : D.MechanicalData)
    (horder : Definition19PathOrder M) :
    D.path.StartsAt
      (D.deformation.step D.firstIndex).introduced := by
  rw [← D.activePath_eq D.firstIndex]
  refine
    ⟨(M.stepLabeling D.firstIndex).introducedPathIndex,
      M.firstIntroducedIndex_val_eq_zero horder, ?_⟩
  exact (M.stepLabeling D.firstIndex).introduced_eq

end MechanicalData

/-- The only local fact still needed at the first step: a dependent vertex
has no path neighbor other than the introduced endpoint. -/
def BaseUniquePathNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃u : V⦄,
    u ∈ D.dependentAt 0 →
    ∀ q : Fin D.path.card,
      G.Adj u (D.path.vertex q) →
      D.path.vertex q =
        (D.deformation.step D.firstIndex).introduced

/-- Definition 19's order supplies the endpoint field; the remaining local
neighbor rule supplies the other field of `BaseStepData`. -/
theorem baseStepData_of_pathOrder
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (horder : Definition19PathOrder M)
    (hunique : D.BaseUniquePathNeighborRule) :
    D.BaseStepData where
  startsAt := M.startsAt_firstIntroduced horder
  uniquePathNeighbor := by
    intro u hu q huq
    exact hunique hu q huq

/-- The base dependent vertex anticommutes once the path order and the
remaining local neighbor fact are supplied. -/
theorem baseDependentAnticommutes_of_pathOrder
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (horder : Definition19PathOrder M)
    (hunique : D.BaseUniquePathNeighborRule)
    {u : V} (hu : u ∈ D.dependentAt 0) :
    D.path.AnticommutesWith u :=
  D.baseDependentAnticommutes
    (D.baseStepData_of_pathOrder M horder hunique) hu

/-- The base ordering and local attachment rule give the complete
common-`C_b` predecessor rule. -/
theorem commonBPredecessorRule_of_pathOrder_and_attachingPredecessors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hunique : D.BaseUniquePathNeighborRule)
    (hattach : D.OneOrTwoStepPredecessorAlongBNeighborsRule) :
    O.CommonBPredecessorRule
      .ac D.dependentAt D.path.AnticommutesWith :=
  D.commonBPredecessorRule_of_attachingPredecessors
    M hclaw
    (D.baseStepData_of_pathOrder M horder hunique)
    hattach

/-- Concrete Lemma 11(b) with the base endpoint now derived from
Definition 19's ordered labeling. -/
theorem lemma11b_of_ccTriples_pathOrder_and_attachingPredecessors
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
    (horder : Definition19PathOrder M)
    (hunique : D.BaseUniquePathNeighborRule)
    (hattach : D.OneOrTwoStepPredecessorAlongBNeighborsRule)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hcomm : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 ∧
      O.EarlierAnticommutingWitnessInUniquePath
        D.dependentAt D.path.AnticommutesWith s u :=
  D.lemma11b_of_ccTriples_and_attachingPredecessors
    M hclaw hside hEven htriple
    (D.baseStepData_of_pathOrder M horder hunique)
    hattach hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
