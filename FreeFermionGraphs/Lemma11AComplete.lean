import FreeFermionGraphs.Lemma11AFullDefinition19History
import FreeFermionGraphs.Lemma11AConcretePairing

/-!
# Lemma 11(a): assembled Definition 19 theorem

This is the direct assembly of the three parts of Lemma 11(a) at the full
Definition 19 history interface: the path-block membership equivalence, the
same-pairing common neighbour, and the original-hole degree-three / opposite
clone equivalence.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Complete assembled form of Lemma 11(a) for an `(a,c)` Definition 19
path block and its finite history of earlier blocks.  The global history data
derives the no-earlier-anticommutation conclusion used in the degree clause.
-/
theorem lemma11a_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (hanti : D.path.AnticommutesWith u)
    (horiginalOutside :
      u ∉ Set.range (X.history.block 0).initialHole.vertex)
    (hcurrentInitialOutside : u ∉ Set.range D.initialHole.vertex)
    (hcloneInCa : ∀ q : Fin (X.history.block 0).initialHole.card,
      (X.history.block 0).initialHole.SingleVertexDeformation u q →
        (X.history.block 0).initialHole.vertex q ∈ O.Ca) :
    ((∃ t : Nat, u ∈ D.dependentAt t) ↔
      u ≠ (D.deformation.step D.firstIndex).introduced ∧
        D.finalHole.externalDegree u =
          D.initialHole.externalDegree u + 1) ∧
      (∃ v,
        v ∈ Set.range
            (D.deformation.step
              ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex ∧
          v ∈ Set.range
            (D.deformation.step
              ⟨s, D.index_lt_of_mem_dependentAt hu⟩).after.vertex ∧
          G.Adj u v ∧
          G.Adj
            (D.deformation.step
              ⟨s, D.index_lt_of_mem_dependentAt hu⟩).introduced v ∧
          G.Adj
            ((D.deformation.step
              ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex
                (D.deformation.step
                  ⟨s, D.index_lt_of_mem_dependentAt hu⟩).removedIndex) v ∧
          O.HasPairingType .ac u v) ∧
      (D.finalHole.externalDegree u = 4 ↔
        (X.history.block 0).initialHole.externalDegree u = 3 ∧
          O.HasTypedClone .ad (X.history.block 0).initialHole u) := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hui : u ∈ (D.deformation.step i).dependentSet := by
    exact D.mem_step_dependentSet_of_mem_dependentAt hu
  have huPrime : u ∈ Cprime :=
    ((ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step i)).1 hui).1
  have huCd : u ∈ O.Cd :=
    (D.deformation.step i).dependent_mem_cd
      (X.current.neighborhood.mechanical.stepGeometry i) hui
  have huClass : u ∈ PairingType.ac.classFromB O.Cc O.Cd := by
    simpa using huCd
  refine ⟨D.lemma11a_membership_iff_ne_first_and_degree
    X.current hclaw huPrime hanti, ?_, ?_⟩
  · exact D.lemma11ai_same_pairing_of_fullDefinition19
      X.current hclaw hu
  · simpa using
      (D.lemma11aii_of_fullDefinition19History
        X hclaw .ac hu huPrime hanti horiginalOutside
        hcurrentInitialOutside hcloneInCa huClass)

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
