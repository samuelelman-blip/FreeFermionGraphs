import FreeFermionGraphs.ObstructionSearchFiniteMixedExecutableTerminalEvent
import FreeFermionGraphs.ObstructionSearchFiniteMixedCommutingTerminalEvent
import FreeFermionGraphs.ObstructionSearchFiniteMixedCrossCorollary11
import FreeFermionGraphs.ObstructionSearchFiniteMixedContextExact

/-!
# Terminal target commutation from literal stopping geometry

In the interior two-incoming branch of manuscript Lemma 14, the common target
is not on any path appended by either incoming search. If it anticommuted with
one actual path, Lemma 11(a) would put it in that block's dependent set and
force degree four. Corollary 11 excludes anticommutation with every later path,
so the remaining commuting suffix preserves even degree parity. This
contradicts the literal terminal clone, which has degree three in the exact
final hole.

The argument below derives path commutation. It is not stored in the terminal
search event.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- The right-to-left content of Lemma 11(a)'s first equivalence, stated
without redundantly asking for the degree equality that the proof itself
derives. -/
theorem exists_dependentAt_of_ne_first_of_anticommutes
    (D : ConcretePathDeformation O Cprime)
    (F : D.FullDefinition19Lemma11AData)
    (hclaw : G.IsClawFree)
    {u : V}
    (huPrime : u ∈ Cprime)
    (huNeFirst : u ≠
      (D.deformation.step D.firstIndex).introduced)
    (hanti : D.path.AnticommutesWith u) :
    ∃ s : Nat, u ∈ D.dependentAt s := by
  have huOutside :=
    F.anticommuting_not_mem_path huPrime huNeFirst hanti
  have hbalance := D.anticommuting_neighborCount_balance
    F.neighborhood.pathOrder F.path_card_eq hclaw
    huOutside hanti
    (F.terminalAnticommutingNonadjacency
      huPrime huOutside hanti)
    (D.removedIntroducedRemovedExtension_of_fullDefinition19
      F hclaw huPrime)
  rw [D.introducedNeighborCount_eq_ncard,
    D.removedNeighborCount_eq_ncard] at hbalance
  have hnsub :
      ¬D.introducedNeighborStepSet u ⊆
        D.removedNeighborStepSet u := by
    intro hsub
    have hle := Set.ncard_le_ncard hsub
    omega
  obtain ⟨i, hiIntroduced, hiNotRemoved⟩ :=
    Set.not_subset.mp hnsub
  have hiAdj : G.Adj u (D.deformation.step i).introduced :=
    hiIntroduced
  have hiNotAdj : ¬G.Adj u
      ((D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex) :=
    hiNotRemoved
  have hiNe : u ≠
      (D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex := by
    intro h
    apply huOutside
    refine ⟨F.neighborhood.pathOrder.removedPathIndex i, ?_⟩
    rw [F.neighborhood.pathOrder.removed_eq i]
    exact h.symm
  refine ⟨i.val, (D.mem_dependentAt_iff_definition20).2 ?_⟩
  exact ⟨i.isLt, huPrime, hiAdj, hiNe, hiNotAdj⟩

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- A commuting finite block preserves external-degree parity. -/
theorem finalDegree_mod_two_eq_initial_of_commutes
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) (u : V)
    (hcomm : (X.block i).path.CommutesWith u) :
    (X.block i).finalHole.externalDegree u % 2 =
      (X.block i).initialHole.externalDegree u % 2 := by
  let A := X.orientedBlock i
  have hcommA : A.path.CommutesWith u := by
    simpa [A, FiniteMixedSideSearchTrace.orientedBlock] using hcomm
  have hparity :=
    A.finalDegree_mod_two_eq_initial_of_commutes
      (X.localData i).neighborhood.pathOrder
      (X.localData i).path_card_eq u hcommA
  simpa only [A, FiniteMixedSideSearchTrace.orientedBlock,
    ConcretePathDeformation.reorient_finalHole,
    ConcretePathDeformation.reorient_initialHole] using hparity

/-- Once block `q` has even degree and every later path commutes, the last
block-final degree has the same parity. -/
theorem lastFinalDegree_mod_two_eq_of_commuting_suffix
    (X : FiniteMixedSideSearchTrace S originalHole)
    (u : V)
    (q : Fin X.blockCount)
    (hcomm : ∀ r : Fin X.blockCount,
      q.val < r.val → (X.block r).path.CommutesWith u) :
    (X.block X.lastBlockIndex).finalHole.externalDegree u % 2 =
      (X.block q).finalHole.externalDegree u % 2 := by
  have hthrough :
      ∀ n : Nat, ∀ hn : n < X.blockCount,
        q.val ≤ n →
        (X.block ⟨n, hn⟩).finalHole.externalDegree u % 2 =
          (X.block q).finalHole.externalDegree u % 2 := by
    intro n
    induction n with
    | zero =>
        intro hn hqn
        have hqzero : q.val = 0 := by omega
        have hidx : (⟨0, hn⟩ : Fin X.blockCount) = q :=
          Fin.ext hqzero.symm
        rw [hidx]
    | succ n ih =>
        intro hn hqn
        by_cases hEq : q.val = n + 1
        · have hidx : (⟨n + 1, hn⟩ : Fin X.blockCount) = q :=
            Fin.ext hEq.symm
          rw [hidx]
        · have hqle : q.val ≤ n := by omega
          have hnPrevious : n < X.blockCount := by omega
          let previous : Fin X.blockCount := ⟨n, hnPrevious⟩
          let current : Fin X.blockCount := ⟨n + 1, hn⟩
          have hqcurrent : q.val < current.val := by
            dsimp [current]
            omega
          have hparity :=
            X.finalDegree_mod_two_eq_initial_of_commutes current u
              (hcomm current hqcurrent)
          have hchain :
              Set.range (X.block previous).finalHole.vertex =
                Set.range (X.block current).initialHole.vertex :=
            X.chain (by simp [previous, current])
          have hdegree :
              (X.block previous).finalHole.externalDegree u =
                (X.block current).initialHole.externalDegree u :=
            (X.block previous).finalHole.externalDegree_eq_of_range_eq
              (X.block current).initialHole hchain
          calc
            (X.block ⟨n + 1, hn⟩).finalHole.externalDegree u % 2 =
                (X.block current).initialHole.externalDegree u % 2 := by
              simpa [current] using hparity
            _ = (X.block previous).finalHole.externalDegree u % 2 := by
              rw [← hdegree]
            _ = (X.block q).finalHole.externalDegree u % 2 := by
              simpa [previous] using ih hnPrevious hqle
  exact hthrough X.lastBlockIndex.val X.lastBlockIndex.isLt
    (by
      dsimp [FiniteMixedSideSearchTrace.lastBlockIndex]
      omega)

end FiniteMixedSideSearchTrace
end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {I : ObstructionSearchInitialization families Cprime}

namespace ObstructionSearchInitialization

namespace FiniteMixedSideOSExecution

/-- Distinct indices of one literal nonempty execution carry distinct path
components. -/
theorem block_path_ne
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    {q r : Fin X.toOrdered.blockCount}
    (hne : q ≠ r) :
    Set.range (X.toOrdered.block q).path.vertex ≠
      Set.range (X.toOrdered.block r).path.vertex := by
  cases X with
  | empty hrun => exact Fin.elim0 q
  | nonempty data =>
      simpa [FiniteMixedSideOSExecution.toOrdered] using
        data.literal.trace.path_pairwise hne

/-- Parity transport from one block through the later commuting suffix, stated
on the exact manuscript final hole of the empty/nonempty execution wrapper. -/
theorem manuscriptFinalHole_degree_mod_two_eq_of_commuting_suffix
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    (u : V)
    (q : Fin X.toOrdered.blockCount)
    (hcomm : ∀ r : Fin X.toOrdered.blockCount,
      q.val < r.val → (X.toOrdered.block r).path.CommutesWith u) :
    X.toOrdered.manuscriptFinalHole.externalDegree u % 2 =
      (X.toOrdered.block q).finalHole.externalDegree u % 2 := by
  cases X with
  | empty hrun => exact Fin.elim0 q
  | nonempty data =>
      let trace := data.literal.trace
      have hcommTrace : ∀ r : Fin trace.blockCount,
          q.val < r.val → (trace.block r).path.CommutesWith u := by
        intro r hqr
        simpa [trace, FiniteMixedSideOSExecution.toOrdered] using
          hcomm r hqr
      have hparity :=
        trace.lastFinalDegree_mod_two_eq_of_commuting_suffix
          u q hcommTrace
      let ordered := (FiniteMixedSideOSExecution.nonempty data).toOrdered
      have hpos : 0 < ordered.blockCount := Nat.zero_lt_of_lt q.isLt
      have hfinal := ordered.manuscriptFinalHole_eq_lastBlockFinalHole hpos
      have hindex : ordered.lastBlockIndex hpos = trace.lastBlockIndex := by
        apply Fin.ext
        rfl
      rw [hfinal, hindex]
      simpa [ordered, trace, FiniteMixedSideOSExecution.toOrdered] using hparity

end FiniteMixedSideOSExecution

/-- Definition 20's literal fact that every initializer belongs to the fixed
prime-hole carrier. -/
structure InitializationPrimeVertexData
    (I : ObstructionSearchInitialization families Cprime) : Prop where
  node_mem_prime : ∀ j : I.Node, (j : V) ∈ Cprime

namespace InitializationFiniteMixedSideTerminalCoreData

/-- Anticommutation of a target with an actual block forces target membership
in that block's dependent set. -/
theorem target_mem_dependentAt_of_anticommutes
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (P : I.InitializationPrimeVertexData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (q : Fin
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount)
    (hanti :
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block q).path.AnticommutesWith (target : V)) :
    ∃ s : Nat,
      (target : V) ∈
        ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).block q).dependentAt s := by
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  let D := (Y.ordered source).block q
  let side := (Y.ordered source).side q
  let A := D.reorient side
  have hData : A.FullDefinition19Lemma11AData := by
    simpa [A, D, side, Y] using (Y.ordered source).localData q
  have hantiA : A.path.AnticommutesWith (target : V) := by
    simpa [A, D, ConcretePathDeformation.reorient_path] using hanti
  have hneFirst :
      (target : V) ≠
        (A.deformation.step A.firstIndex).introduced := by
    intro hEq
    have hmemA : (target : V) ∈ Set.range A.path.vertex := by
      refine ⟨hData.neighborhood.pathOrder.introducedPathIndex A.firstIndex, ?_⟩
      rw [hData.neighborhood.pathOrder.introduced_eq A.firstIndex]
      exact hEq.symm
    apply T.target_not_mem_executionPath incoming q
    simpa [A, D, ConcretePathDeformation.reorient_path] using hmemA
  obtain ⟨s, hs⟩ :=
    A.exists_dependentAt_of_ne_first_of_anticommutes
      hData hclaw (P.node_mem_prime target) hneFirst hantiA
  refine ⟨s, ?_⟩
  change (target : V) ∈ (D.reorient side).dependentAt s at hs
  rw [D.reorient_dependentAt side s] at hs
  exact hs

/-- The literal final clone at a terminal stop forces the target to commute
with every actual path in the incoming finite execution. -/
theorem target_commutes_executionPath
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (P : I.InitializationPrimeVertexData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    {C : FiniteMixedSideTerminalComponentExecution T target}
    (E : FiniteMixedSideIncomingTerminalStopExecution
      T C source target incoming)
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
  obtain ⟨cloneIndex, hclone, _hpair⟩ := htyped
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
  have hfinalEven :
      X.manuscriptFinalHole.externalDegree (target : V) % 2 = 0 := by
    rw [hparity, hfour]
  have hpos : 0 < X.blockCount := Nat.zero_lt_of_lt q.isLt
  obtain ⟨i, hterminalClone⟩ := E.positive_target_clone hpos
  have hterminalThree :
      X.manuscriptFinalHole.externalDegree (target : V) = 3 :=
    hterminalClone.externalDegree_eq_three
  rw [hterminalThree] at hfinalEven
  omega

end InitializationFiniteMixedSideTerminalCoreData

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
