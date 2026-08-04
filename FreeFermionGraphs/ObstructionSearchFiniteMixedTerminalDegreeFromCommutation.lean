import FreeFermionGraphs.ObstructionSearchFiniteMixedFinalCarrierProvenance
import FreeFermionGraphs.ObstructionSearchFiniteMixedLemma11A
import FreeFermionGraphs.ObstructionSearchFiniteMixedGeneratedTerminalEvent

/-!
# Terminal degree three from commuting execution paths

The distinct-centre branch of manuscript Lemma 14 first proves that the common
obstruction target is outside every execution path and commutes with every path
operator. The target is a clone in the initialized original hole, so its
original external degree is three. A commuting Definition 19 block preserves
external-degree parity. Every intermediate hole is even, and Lemma 7 excludes
all odd external degrees other than three.

This module formalizes that argument directly. It replaces the stronger
stepwise `TargetBalanced` premise by the manuscript-level assertion that the
target commutes with every actual finite execution path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation
namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

private theorem oriented_finalDegree_parity
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

private theorem block_finalHole_even
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    Even (X.block i).finalHole.card := by
  let A := X.orientedBlock i
  have hinitial : Even A.initialHole.card :=
    (X.localData i).neighborhood.alternating.initialHole_even
  have hfinal : A.finalHole.card = A.initialHole.card :=
    A.finalHole_card_eq_initialHole_card
  have hfinalEven : Even A.finalHole.card := by
    rw [hfinal]
    exact hinitial
  simpa only [A, FiniteMixedSideSearchTrace.orientedBlock,
    ConcretePathDeformation.reorient_finalHole] using hfinalEven

/-- If an external vertex starts with degree three and commutes with every
actual path, then it has degree three at the end of every finite block. -/
theorem blockFinal_externalDegree_eq_three_of_commutes
    (X : FiniteMixedSideSearchTrace S originalHole)
    (hclaw : G.IsClawFree)
    {u : V}
    (horiginal : originalHole.externalDegree u = 3)
    (hcomm : ∀ i : Fin X.blockCount,
      (X.block i).path.CommutesWith u)
    (i : Fin X.blockCount) :
    (X.block i).finalHole.externalDegree u = 3 := by
  have hthrough :
      ∀ n : Nat, ∀ hn : n < X.blockCount,
        (X.block ⟨n, hn⟩).finalHole.externalDegree u = 3 := by
    intro n
    induction n with
    | zero =>
        intro hn
        let current : Fin X.blockCount := ⟨0, hn⟩
        have hinitial :
            (X.block current).initialHole.externalDegree u =
              originalHole.externalDegree u :=
          (X.block current).initialHole.externalDegree_eq_of_range_eq
            originalHole (by simpa [current] using X.originalHole_eq)
        have hparity := X.oriented_finalDegree_parity current u (hcomm current)
        have hodd :
            (X.block current).finalHole.externalDegree u % 2 = 1 := by
          rw [hparity, hinitial, horiginal]
        exact
          (X.block current).finalHole.externalDegree_eq_three_of_even_and_odd_any
            hclaw (X.block_finalHole_even current) hodd
    | succ n ih =>
        intro hn
        have hnPrevious : n < X.blockCount := by omega
        let previous : Fin X.blockCount := ⟨n, hnPrevious⟩
        let current : Fin X.blockCount := ⟨n + 1, hn⟩
        have hprevious :
            (X.block previous).finalHole.externalDegree u = 3 :=
          ih hnPrevious
        have hchain :
            Set.range (X.block previous).finalHole.vertex =
              Set.range (X.block current).initialHole.vertex :=
          X.chain (by simp [previous, current])
        have hinitial :
            (X.block current).initialHole.externalDegree u = 3 := by
          have hdegree :
              (X.block previous).finalHole.externalDegree u =
                (X.block current).initialHole.externalDegree u :=
            (X.block previous).finalHole.externalDegree_eq_of_range_eq
              (X.block current).initialHole hchain
          exact hdegree.symm.trans hprevious
        have hparity := X.oriented_finalDegree_parity current u (hcomm current)
        have hodd :
            (X.block current).finalHole.externalDegree u % 2 = 1 := by
          rw [hparity, hinitial]
        exact
          (X.block current).finalHole.externalDegree_eq_three_of_even_and_odd_any
            hclaw (X.block_finalHole_even current) hodd
  exact hthrough i.val i.isLt

end FiniteMixedSideSearchTrace
end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {I : ObstructionSearchInitialization families Cprime}

namespace ObstructionSearchInitialization
namespace FiniteMixedSideOSExecution

/-- A positive finite execution whose paths all commute with `u` preserves an
initial external degree of three on the exact manuscript final hole. -/
theorem manuscriptFinalHole_externalDegree_eq_three_of_commutes
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    (hclaw : G.IsClawFree)
    {u : V}
    (horiginal : originalHole.externalDegree u = 3)
    (hcomm : ∀ q : Fin X.toOrdered.blockCount,
      (X.toOrdered.block q).path.CommutesWith u)
    (hpos : 0 < X.toOrdered.blockCount) :
    X.toOrdered.manuscriptFinalHole.externalDegree u = 3 := by
  cases X with
  | empty hrun =>
      simp [FiniteMixedSideOSExecution.toOrdered] at hpos
  | nonempty data =>
      let trace := data.literal.trace
      let last : Fin trace.blockCount := trace.lastBlockIndex
      have hcommTrace : ∀ i : Fin trace.blockCount,
          (trace.block i).path.CommutesWith u := by
        intro i
        simpa [trace, FiniteMixedSideOSExecution.toOrdered] using hcomm i
      have hlast :=
        trace.blockFinal_externalDegree_eq_three_of_commutes
          hclaw horiginal hcommTrace last
      let ordered := (FiniteMixedSideOSExecution.nonempty data).toOrdered
      have hfinal := ordered.manuscriptFinalHole_eq_lastBlockFinalHole hpos
      have hindex : ordered.lastBlockIndex hpos = last := by
        apply Fin.ext
        rfl
      rw [hfinal]
      change
        (data.literal.trace.block (ordered.lastBlockIndex hpos)).finalHole.externalDegree
          u = 3
      rw [hindex]
      exact hlast

end FiniteMixedSideOSExecution

namespace InitializationFiniteMixedSideTerminalCoreData

/-- The manuscript's commutation assertion implies exact degree three in the
positive terminal hole. No stepwise target-balance certificate is used. -/
theorem positive_finalDegree_three_of_executionPaths_commute
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (hclaw : G.IsClawFree)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (hcomm :
      ∀ q : Fin
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount,
        ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).block q).path.CommutesWith (target : V))
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.externalDegree (target : V) = 3 := by
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  let E := Y.execution source
  obtain ⟨i, hi⟩ := T.exists_target_clone_of_incoming hclaw incoming
  have horiginal : Y.originalHole.externalDegree (target : V) = 3 :=
    hi.externalDegree_eq_three
  exact E.manuscriptFinalHole_externalDegree_eq_three_of_commutes
    hclaw horiginal hcomm hpos

end InitializationFiniteMixedSideTerminalCoreData
end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
