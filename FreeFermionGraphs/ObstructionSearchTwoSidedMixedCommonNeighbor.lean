import FreeFermionGraphs.ObstructionSearchTwoSidedMixedPersistence

/-!
# Common-neighbour transport through mixed-side Definition 19 histories

Lemma 11(a.i) supplies a common original-hole neighbour for the base dependent
set of each path block.  In a mixed-side history the local colour statement is
read in that block's selected orientation, while the underlying hole carrier is
transported through the one literal Definition 19 sequence.

This module proves the prior-block and current-block transport statements.  It
does not construct an obstruction-search execution and does not assume any
conclusion of Lemma 14.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- The base-step common neighbour of an earlier mixed-side block belongs to
    the first hole of the literal carrier history.  Its colour is stated in
    that block's selected orientation. -/
theorem priorBaseCommonNeighborOn_of_mixedSideHistory
    (D : ConcretePathDeformation O Cprime)
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree)
    (r : Nat) :
    ((X.history.side r).family O).BaseCommonNeighborOn
      (X.history.orientedBlock r) X.originalHole := by
  intro u hu
  let A := X.history.orientedBlock r
  obtain ⟨v, hvInitial, _hvFinal, huv, hjv, hkv, hvCb, hvNotPrime⟩ :=
    A.lemma11ai_commonNeighbor_currentBlock
      (X.history.localData r) hclaw hu
  have hvOriginal : v ∈ Set.range X.originalHole.vertex := by
    by_cases hr : r = 0
    · subst r
      simpa [A,
        MixedSideFullDefinition19Lemma11AHistoryData.originalHole,
        MixedSidePathBlockHistory.orientedBlock] using hvInitial
    · have hrPos : 0 < r := Nat.pos_of_ne_zero hr
      have hvPreviousFinal :
          v ∈ Set.range
            (X.history.carrier.block (r - 1)).finalHole.vertex := by
        rw [X.history.carrier.chain (r - 1)]
        have hrEq : r - 1 + 1 = r := by omega
        rw [hrEq]
        simpa [A, MixedSidePathBlockHistory.orientedBlock] using hvInitial
      have hvFirst :
          v ∈ Set.range
            (X.history.carrier.block 0).initialHole.vertex :=
        X.history.carrier.mem_firstInitial_of_mem_final_through
          (r - 1) hvPreviousFinal (by
            intro q _hq j hEq
            apply hvNotPrime
            rw [hEq]
            simpa using
              (X.history.localData q).neighborhood.primeHole.introduced_mem j)
      simpa [MixedSideFullDefinition19Lemma11AHistoryData.originalHole] using
        hvFirst
  refine ⟨v, hvOriginal, huv, ?_, ?_, hvCb⟩
  · simpa [A, ConcretePathDeformation.firstIndex] using hjv
  · simpa [A, ConcretePathDeformation.firstIndex] using hkv

/-- The current mixed-side block's base-step common neighbour also belongs to
    the first hole of the preceding literal carrier history.  Its colour is
    stated in the current block's selected orientation. -/
theorem currentBaseCommonNeighborOn_of_mixedSideHistory
    (D : ConcretePathDeformation O Cprime)
    (X : D.MixedSideFullDefinition19Lemma11AHistoryData)
    (hclaw : G.IsClawFree) :
    (X.currentSide.family O).BaseCommonNeighborOn
      X.orientedCurrent X.originalHole := by
  intro u hu
  let A := X.orientedCurrent
  obtain ⟨v, hvCurrentInitial, _hvFinal, huv, hjv, hkv,
      hvCb, hvNotPrime⟩ :=
    A.lemma11ai_commonNeighbor_currentBlock X.current hclaw hu
  let last : Nat := X.priorCount - 1
  have hvLast :
      v ∈ Set.range
        (X.history.carrier.block last).finalHole.vertex := by
    rw [X.final_before_current]
    simpa [A,
      MixedSideFullDefinition19Lemma11AHistoryData.orientedCurrent] using
      hvCurrentInitial
  have hvFirst :
      v ∈ Set.range
        (X.history.carrier.block 0).initialHole.vertex :=
    X.history.carrier.mem_firstInitial_of_mem_final_through last hvLast (by
      intro r _hr j hEq
      apply hvNotPrime
      rw [hEq]
      simpa using
        (X.history.localData r).neighborhood.primeHole.introduced_mem j)
  have hvOriginal : v ∈ Set.range X.originalHole.vertex := by
    simpa [MixedSideFullDefinition19Lemma11AHistoryData.originalHole] using
      hvFirst
  refine ⟨v, hvOriginal, huv, ?_, ?_, hvCb⟩
  · simpa [A, ConcretePathDeformation.firstIndex] using hjv
  · simpa [A, ConcretePathDeformation.firstIndex] using hkv

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph