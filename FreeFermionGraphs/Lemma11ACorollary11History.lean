import FreeFermionGraphs.Lemma11ACorollary11Proof

/-!
# Corollary 11 along a finite Definition 19 history

The common neighbours supplied by the two path blocks are transported back
to the first hole in the history.  The concrete Corollary 11 theorem then
excludes a shared dependent anticommuting witness.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- A base-step common neighbour of history block `r` belongs to the first
initial hole of the history. -/
theorem priorBaseCommonNeighborOn
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    (r : Nat) :
    O.BaseCommonNeighborOn (X.history.block r)
      (X.history.block 0).initialHole := by
  intro u hu
  let A := X.history.block r
  obtain ⟨v, hvInitial, _hvFinal, huv, hjv, hkv, hvCb, hvNotPrime⟩ :=
    A.lemma11ai_commonNeighbor_currentBlock (X.prior r) hclaw hu
  have hvOriginal :
      v ∈ Set.range (X.history.block 0).initialHole.vertex := by
    by_cases hr : r = 0
    · subst r
      simpa [A] using hvInitial
    · have hrPos : 0 < r := Nat.pos_of_ne_zero hr
      have hvPreviousFinal :
          v ∈ Set.range (X.history.block (r - 1)).finalHole.vertex := by
        rw [X.history.chain (r - 1)]
        have hrEq : r - 1 + 1 = r := by omega
        rw [hrEq]
        simpa [A] using hvInitial
      exact X.history.mem_firstInitial_of_mem_final_through
        (r - 1) hvPreviousFinal (by
          intro q _hq j hEq
          apply hvNotPrime
          rw [hEq]
          exact (X.prior q).neighborhood.primeHole.introduced_mem j)
  refine ⟨v, hvOriginal, huv, ?_, ?_, hvCb⟩
  · simpa [A, ConcretePathDeformation.firstIndex] using hjv
  · simpa [A, ConcretePathDeformation.firstIndex] using hkv

/-- The current block's base-step common neighbour also belongs to the
first initial hole of the positive history. -/
theorem currentBaseCommonNeighborOn
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree) :
    O.BaseCommonNeighborOn D (X.history.block 0).initialHole := by
  intro u hu
  obtain ⟨v, hvCurrentInitial, _hvFinal, huv, hjv, hkv,
      hvCb, hvNotPrime⟩ :=
    D.lemma11ai_commonNeighbor_currentBlock X.current hclaw hu
  let last : Nat := X.priorCount - 1
  have hvLast :
      v ∈ Set.range (X.history.block last).finalHole.vertex := by
    rw [X.final_before_current]
    exact hvCurrentInitial
  have hvOriginal :
      v ∈ Set.range (X.history.block 0).initialHole.vertex :=
    X.history.mem_firstInitial_of_mem_final_through last hvLast (by
      intro r _hr j hEq
      apply hvNotPrime
      rw [hEq]
      exact (X.prior r).neighborhood.primeHole.introduced_mem j)
  refine ⟨v, hvOriginal, huv, ?_, ?_, hvCb⟩
  · simpa [ConcretePathDeformation.firstIndex] using hjv
  · simpa [ConcretePathDeformation.firstIndex] using hkv

/-- Corollary 11 for every earlier block relative to the current block,
proved from the finite Definition 19 history. -/
theorem noSharedDependentAnticommutingWitness_of_fullDefinition19History
    (D : ConcretePathDeformation O Cprime)
    (X : D.FullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    {r : Nat} (hr : r < X.priorCount) :
    ¬SharedDependentAnticommutingWitness
      (X.history.block r).path D.path
      (X.history.block r).dependentAt D.dependentAt := by
  let C := (X.history.block 0).initialHole
  have hEven : Even C.card :=
    (X.prior 0).neighborhood.alternating.initialHole_even
  have hcarrier : Set.range C.vertex ⊆ O.Ca ∪ O.Cb := by
    intro x hx
    apply ((X.prior 0).neighborhood.mechanical.stepGeometry
      (X.history.block 0).firstIndex).before_subset
    simpa [C, ConcretePathDeformation.initialHole] using hx
  exact noSharedDependentAnticommutingWitness_of_concreteBlocks
    (X.history.block r) D (X.prior r) X.current C hclaw hEven hcarrier
    (X.priorPath_ne_current r hr)
    (D.priorBaseCommonNeighborOn X hclaw r)
    (D.currentBaseCommonNeighborOn X hclaw)

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
