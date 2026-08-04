import FreeFermionGraphs.ObstructionSearchFiniteMixedFinalCarrierProvenance
import FreeFermionGraphs.ObstructionSearchFiniteMixedLemma11A

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

/-- Every hole in a concrete path block has the same cardinality as the
initial hole. -/
theorem finalHole_card_eq_initialHole_card
    (D : ConcretePathDeformation O Cprime) :
    D.finalHole.card = D.initialHole.card := by
  have hbefore :
      ∀ n : Nat, ∀ hn : n < D.deformation.stepCount,
        (D.deformation.step ⟨n, hn⟩).before.card =
          D.initialHole.card := by
    intro n
    induction n with
    | zero =>
        intro hn
        rfl
    | succ n ih =>
        intro hn
        have hnPrevious : n < D.deformation.stepCount := by omega
        let previous : Fin D.deformation.stepCount := ⟨n, hnPrevious⟩
        let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
        have hchain :
            Set.range (D.deformation.step previous).after.vertex =
              Set.range (D.deformation.step current).before.vertex :=
          D.deformation.carrier_chain (by simp [previous, current])
        have hcard :
            (D.deformation.step previous).after.card =
              (D.deformation.step current).before.card :=
          IndexedInducedHole.card_eq_of_range_eq
            (D.deformation.step previous).after
            (D.deformation.step current).before hchain
        calc
          (D.deformation.step ⟨n + 1, hn⟩).before.card =
              (D.deformation.step current).before.card := by rfl
          _ = (D.deformation.step previous).after.card := hcard.symm
          _ = (D.deformation.step previous).before.card := by rfl
          _ = D.initialHole.card := by
                simpa [previous] using ih hnPrevious
  have hlast : D.deformation.stepCount - 1 < D.deformation.stepCount := by
    omega
  calc
    D.finalHole.card =
        (D.deformation.step D.lastIndex).before.card := by rfl
    _ = D.initialHole.card := by
      simpa [ConcretePathDeformation.lastIndex] using
        hbefore (D.deformation.stepCount - 1) hlast

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
  cases hside : X.side i <;>
    simpa [A, FiniteMixedSideSearchTrace.orientedBlock, hside,
      ConcretePathDeformation.reorient] using hparity

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
  cases hside : X.side i <;>
    simpa [A, FiniteMixedSideSearchTrace.orientedBlock, hside,
      ConcretePathDeformation.reorient] using hfinalEven

/-- If an external vertex starts with degree three, remains outside every
block-final hole, and commutes with every actual path, then it has degree three
at the end of every finite block. -/
theorem blockFinal_externalDegree_eq_three_of_commutes
    (X : FiniteMixedSideSearchTrace S originalHole)
    (hclaw : G.IsClawFree)
    {u : V}
    (horiginal : originalHole.externalDegree u = 3)
    (houtside : ∀ i : Fin X.blockCount,
      u ∉ Set.range (X.block i).finalHole.vertex)
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
          have hdegree :=
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
namespace InitializationFiniteMixedSideTerminalCoreData

/-- A common obstruction target is outside the final hole of every actual
block in an incoming finite execution. -/
theorem target_not_mem_blockFinalHole
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    {source target : I.Node}
    (incoming : I.graph.Arc source target)
    (q : Fin
      (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).blockCount) :
    (target : V) ∉ Set.range
      ((T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
        source).block q).finalHole.vertex := by
  intro htarget
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  let E := Y.execution source
  let X := E.toOrdered
  have htargetX :
      (target : V) ∈ Set.range (X.block q).finalHole.vertex := by
    simpa [X, E, Y,
      InitializationFiniteMixedSideOSExecutionData.ordered] using htarget
  rcases E.mem_originalHole_or_mem_orderedPath_through
      q.val q.isLt htargetX with horiginal | ⟨r, _hrle, hpath⟩
  · exact T.target_not_mem_originalHole target horiginal
  · exact T.target_not_mem_executionPath incoming r hpath

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
  cases hE : E with
  | empty hrun =>
      change 0 < 0 at hpos
      omega
  | nonempty data =>
      let trace := data.literal.trace
      let last : Fin trace.blockCount := trace.lastBlockIndex
      have horiginal : Y.originalHole.externalDegree (target : V) = 3 := by
        obtain ⟨i, hi⟩ := T.exists_target_clone_of_incoming hclaw incoming
        exact hi.externalDegree_eq_three
      have houtside : ∀ i : Fin trace.blockCount,
          (target : V) ∉ Set.range (trace.block i).finalHole.vertex := by
        intro i
        have hordered := T.target_not_mem_blockFinalHole incoming i
        simpa [Y, E, hE, trace,
          InitializationFiniteMixedSideOSExecutionData.ordered,
          FiniteMixedSideOSExecution.toOrdered] using hordered
      have hcommTrace : ∀ i : Fin trace.blockCount,
          (trace.block i).path.CommutesWith (target : V) := by
        intro i
        have h := hcomm i
        simpa [Y, E, hE, trace,
          InitializationFiniteMixedSideOSExecutionData.ordered,
          FiniteMixedSideOSExecution.toOrdered] using h
      have hlast :=
        trace.blockFinal_externalDegree_eq_three_of_commutes
          hclaw horiginal houtside hcommTrace last
      let ordered := E.toOrdered
      have hfinal := ordered.manuscriptFinalHole_eq_lastBlockFinalHole hpos
      have hindex : ordered.lastBlockIndex hpos = last := by
        apply Fin.ext
        rfl
      rw [hfinal]
      change
        (data.literal.trace.block (ordered.lastBlockIndex hpos)).finalHole.externalDegree
          (target : V) = 3
      rw [hindex]
      exact hlast

end InitializationFiniteMixedSideTerminalCoreData
end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
