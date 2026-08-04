import FreeFermionGraphs.ObstructionSearchFiniteMixedTargetCommutation

/-!
# Target commutation from the terminal clone relation

The target-commutation proof uses only the literal positive terminal clone from
the stopping event. It does not depend on the global coordinate presentation of
the terminal path. This module exposes that exact dependency so the strongest
Lemma 14 route need not store target commutation as input.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace InitializationFiniteMixedSideTerminalCoreData

/-- A positive terminal clone forces the target to commute with every actual
path in the incoming finite execution. -/
theorem target_commutes_executionPath_of_positive_target_clone
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (P : I.InitializationPrimeVertexData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (positive_target_clone :
      ∀ hpos :
        0 <
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source).blockCount,
        ∃ i : Fin
            (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
              source).manuscriptFinalHole.card,
          (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
            source).manuscriptFinalHole.SingleVertexDeformation
              (target : V) i)
    (q : Fin
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount) :
    ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block q).path.CommutesWith (target : V) := by
  by_contra hnotCommutes
  have hanti :
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block q).path.AnticommutesWith (target : V) :=
    (((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).block q).path.anticommutesWith_iff_not_commutesWith
        (target : V)).2 hnotCommutes
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  let X := Y.ordered source
  obtain ⟨s, hs⟩ :=
    T.target_mem_dependentAt_of_anticommutes P hclaw incoming q hanti
  have htyped :
      (families (I.pairing source)).HasTypedClone .ad
        Y.originalHole (target : V) :=
    (T.stoppingPairing.branch incoming).typedClone_ad hclaw
  have htypedForExact := htyped
  obtain ⟨cloneIndex, hclone, _hpair⟩ := htypedForExact
  have horiginal : Y.originalHole.externalDegree (target : V) = 3 :=
    hclone.externalDegree_eq_three
  have hfour :
      (X.block q).finalHole.externalDegree (target : V) = 4 :=
    (Y.orderedBlock_lemma11aii_exact source q hclaw hs
      (P.node_mem_prime target) hanti).2 ⟨horiginal, htyped⟩
  have hlaterCommutes : ∀ r : Fin X.blockCount,
      q.val < r.val → (X.block r).path.CommutesWith (target : V) := by
    intro r hqr
    by_contra hnotCommutesR
    have hantiR : (X.block r).path.AnticommutesWith (target : V) :=
      ((X.block r).path.anticommutesWith_iff_not_commutesWith
        (target : V)).2 hnotCommutesR
    obtain ⟨t, ht⟩ :=
      T.target_mem_dependentAt_of_anticommutes P hclaw incoming r hantiR
    have hqrNe : q ≠ r := by
      intro hEq
      have hval := congrArg Fin.val hEq
      omega
    have hpathNe :
        Set.range (X.block q).path.vertex ≠
          Set.range (X.block r).path.vertex :=
      (Y.execution source).block_path_ne hqrNe
    have hno :=
      (Y.orderedContextAt source q).noSharedDependentAnticommutingWitness
        (Y.orderedContextAt source r) hclaw hpathNe
    exact hno ⟨target, s, t, hs, ht, hanti, hantiR⟩
  have hparity :=
    (Y.execution source).manuscriptFinalHole_degree_mod_two_eq_of_commuting_suffix
      (target : V) q hlaterCommutes
  have hparityX :
      X.manuscriptFinalHole.externalDegree (target : V) % 2 =
        (X.block q).finalHole.externalDegree (target : V) % 2 := by
    simpa [X, InitializationFiniteMixedSideOSExecutionData.ordered] using hparity
  have hfinalEven :
      X.manuscriptFinalHole.externalDegree (target : V) % 2 = 0 := by
    rw [hparityX, hfour]
  have hpos : 0 < X.blockCount := Nat.zero_lt_of_lt q.isLt
  obtain ⟨i, hterminalClone⟩ := positive_target_clone hpos
  have hterminalThree :
      X.manuscriptFinalHole.externalDegree (target : V) = 3 :=
    hterminalClone.externalDegree_eq_three
  rw [hterminalThree] at hfinalEven
  omega

end InitializationFiniteMixedSideTerminalCoreData
end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
