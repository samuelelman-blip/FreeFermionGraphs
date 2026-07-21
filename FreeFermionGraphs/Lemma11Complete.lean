import FreeFermionGraphs.Lemma11AComplete
import FreeFermionGraphs.Lemma11BFullDefinition19

/-!
# Lemma 11

The manuscript's anticommuting and commuting cases are assembled here for a
vertex of the prime hole and one complete Definition 19 path block.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Complete Lemma 11.  The first conjunct is part (a), including (i) and
(ii); the second conjunct is part (b), including strict descent and the
unique same-pairing path conclusion. -/
theorem lemma11
    (D : ConcretePathDeformation O Cprime)
    (X : D.Lemma11AHistoryContext)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime) :
    (D.path.AnticommutesWith u →
      (((∃ s : Nat, u ∈ D.dependentAt s) ↔
        u ≠ (D.deformation.step D.firstIndex).introduced ∧
          D.finalHole.externalDegree u =
            D.initialHole.externalDegree u + 1) ∧
      (∀ (s : Nat), u ∈ D.dependentAt s →
        ∀ q : Fin D.finalHole.card,
          D.finalHole.externalDegree u = 3 →
          D.finalHole.SingleVertexDeformation u q →
            D.finalHole.vertex q ∈ Set.range X.originalHole.vertex ∧
              O.HasPairingType .ac u (D.finalHole.vertex q)) ∧
      (∀ (s : Nat), u ∈ D.dependentAt s →
        (D.finalHole.externalDegree u = 4 ↔
          X.originalHole.externalDegree u = 3 ∧
            O.HasTypedClone .ad X.originalHole u)))) ∧
    (∀ (s : Nat), u ∈ D.dependentAt s →
      ¬D.path.AnticommutesWith u →
        D.finalDegree s u = 4 ∧
          O.EarlierAnticommutingWitnessInUniqueBDPath
            D.dependentAt D.path.AnticommutesWith s u) := by
  constructor
  · intro hanti
    exact D.lemma11a_complete X hclaw huPrime hanti
  · intro s hu hcomm
    exact D.lemma11b_of_fullDefinition19NeighborhoodData
      X.currentData.neighborhood hclaw hu hcomm

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
