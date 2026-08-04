import FreeFermionGraphs.ObstructionSearchFiniteMixedExecutableTerminalEvent

/-!
# Terminal-target balance through literal finite executions

Before the obstruction search reaches its terminal component, every concrete
replacement preserves adjacency of the eventual obstruction target: the target
is adjacent to the introduced vertex exactly when it is adjacent to the removed
vertex.  This is the step-level invariant which keeps the target's external
degree equal to its original-hole degree.

The invariant is proved stable under the literal one-block and `snoc`
constructors.  Consequently the degree-three conclusion used by Lemma 14 is
derived from the stopping-branch clone on the original hole, rather than stored
as terminal certificate data.
-/

universe u

variable {V : Type u}

namespace SimpleGraph
namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- A complete path block preserves adjacency of `u` at each literal
single-vertex replacement. -/
def TargetBalanced
    (D : ConcretePathDeformation O Cprime) (u : V) : Prop :=
  ∀ s : Fin D.deformation.stepCount,
    G.Adj u (D.deformation.step s).introduced ↔
      G.Adj u
        ((D.deformation.step s).before.vertex
          (D.deformation.step s).removedIndex)

/-- Degree after step `n` equals the degree on the block's initial hole when
all preceding literal replacements are target-balanced. -/
theorem stepAfter_externalDegree_eq_initial_of_targetBalanced
    (D : ConcretePathDeformation O Cprime) (u : V)
    (hbalanced : D.TargetBalanced u)
    (n : Nat) (hn : n < D.deformation.stepCount) :
    (D.deformation.step ⟨n, hn⟩).after.externalDegree u =
      D.initialHole.externalDegree u := by
  induction n with
  | zero =>
      let current : Fin D.deformation.stepCount := ⟨0, hn⟩
      have hstep :=
        (D.deformation.step current).deformation.externalDegree_deform_eq
          (hbalanced current)
      simpa [current, ConcreteDeformationStep.after,
        ConcretePathDeformation.initialHole,
        ConcretePathDeformation.firstIndex] using hstep
  | succ n ih =>
      have hnPrevious : n < D.deformation.stepCount := by omega
      let previous : Fin D.deformation.stepCount := ⟨n, hnPrevious⟩
      let current : Fin D.deformation.stepCount := ⟨n + 1, hn⟩
      have hstep :
          (D.deformation.step current).after.externalDegree u =
            (D.deformation.step current).before.externalDegree u := by
        exact
          (D.deformation.step current).deformation.externalDegree_deform_eq
            (hbalanced current)
      have hchain :
          Set.range (D.deformation.step previous).after.vertex =
            Set.range (D.deformation.step current).before.vertex :=
        D.deformation.carrier_chain (by simp [previous, current])
      have hmiddle :
          (D.deformation.step previous).after.externalDegree u =
            (D.deformation.step current).before.externalDegree u :=
        (D.deformation.step previous).after.externalDegree_eq_of_range_eq
          (D.deformation.step current).before hchain
      calc
        (D.deformation.step ⟨n + 1, hn⟩).after.externalDegree u =
            (D.deformation.step current).before.externalDegree u := by
              simpa [current] using hstep
        _ = (D.deformation.step previous).after.externalDegree u :=
              hmiddle.symm
        _ = D.initialHole.externalDegree u := by
              simpa [previous] using ih hnPrevious

/-- A target-balanced literal path block preserves external degree exactly. -/
theorem finalHole_externalDegree_eq_initial_of_targetBalanced
    (D : ConcretePathDeformation O Cprime) (u : V)
    (hbalanced : D.TargetBalanced u) :
    D.finalHole.externalDegree u = D.initialHole.externalDegree u := by
  have hlast : D.deformation.stepCount - 1 < D.deformation.stepCount := by
    omega
  simpa [ConcretePathDeformation.finalHole,
    ConcretePathDeformation.lastIndex] using
    D.stepAfter_externalDegree_eq_initial_of_targetBalanced
      u hbalanced (D.deformation.stepCount - 1) hlast

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Every literal block in the bounded trace is target-balanced. -/
def TargetBalanced
    (X : FiniteMixedSideSearchTrace S originalHole) (u : V) : Prop :=
  ∀ i : Fin X.blockCount, (X.block i).TargetBalanced u

/-- The one-block constructor preserves the target-balance invariant. -/
theorem targetBalanced_single
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (D.reorient side).FullDefinition19Lemma11AData)
    (hOriginal : Set.range D.initialHole.vertex =
      Set.range originalHole.vertex)
    (hRemoved : ∀ s : Fin D.deformation.stepCount,
      (D.deformation.step s).before.vertex
          (D.deformation.step s).removedIndex ∈
        Set.range originalHole.vertex)
    (hUnique : O.IsUniqueContainingPath
      (D.deformation.step D.firstIndex).introduced
      (Set.range D.path.vertex))
    (u : V) (hbalanced : D.TargetBalanced u) :
    (FiniteMixedSideSearchTrace.single
      D side F hOriginal hRemoved hUnique).TargetBalanced u := by
  intro i
  exact hbalanced

/-- Appending one literal block preserves target balance precisely when the
new block satisfies the same local adjacency invariant. -/
theorem targetBalanced_snoc
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (side : DeformationSide)
    (F : (D.reorient side).FullDefinition19Lemma11AData)
    (hchain :
      Set.range (X.block X.lastBlockIndex).finalHole.vertex =
        Set.range D.initialHole.vertex)
    (hRemoved : ∀ s : Fin D.deformation.stepCount,
      (D.deformation.step s).before.vertex
          (D.deformation.step s).removedIndex ∈
        Set.range originalHole.vertex)
    (hFresh : ∀ i : Fin X.blockCount,
      Set.range (X.block i).path.vertex ≠ Set.range D.path.vertex)
    (hUnique : O.IsUniqueContainingPath
      (D.deformation.step D.firstIndex).introduced
      (Set.range D.path.vertex))
    (u : V)
    (hX : X.TargetBalanced u)
    (hD : D.TargetBalanced u) :
    (X.snoc D side F hchain hRemoved hFresh hUnique).TargetBalanced u := by
  intro i
  refine Fin.lastCases ?_ (fun old => ?_) i
  · simpa [FiniteMixedSideSearchTrace.snoc] using hD
  · simpa [FiniteMixedSideSearchTrace.snoc] using hX old

/-- Degree transport through the first `n+1` target-balanced literal blocks. -/
theorem blockFinal_externalDegree_eq_original_through
    (X : FiniteMixedSideSearchTrace S originalHole)
    (u : V) (hbalanced : X.TargetBalanced u)
    (n : Nat) (hn : n < X.blockCount) :
    (X.block ⟨n, hn⟩).finalHole.externalDegree u =
      originalHole.externalDegree u := by
  induction n with
  | zero =>
      have hblock :=
        (X.block ⟨0, hn⟩).finalHole_externalDegree_eq_initial_of_targetBalanced
          u (hbalanced ⟨0, hn⟩)
      have hinitial :
          (X.block ⟨0, hn⟩).initialHole.externalDegree u =
            originalHole.externalDegree u :=
        (X.block ⟨0, hn⟩).initialHole.externalDegree_eq_of_range_eq
          originalHole (by simpa using X.originalHole_eq)
      exact hblock.trans hinitial
  | succ n ih =>
      have hnPrevious : n < X.blockCount := by omega
      let previous : Fin X.blockCount := ⟨n, hnPrevious⟩
      let current : Fin X.blockCount := ⟨n + 1, hn⟩
      have hblock :
          (X.block current).finalHole.externalDegree u =
            (X.block current).initialHole.externalDegree u :=
        (X.block current).finalHole_externalDegree_eq_initial_of_targetBalanced
          u (hbalanced current)
      have hchain :
          Set.range (X.block previous).finalHole.vertex =
            Set.range (X.block current).initialHole.vertex :=
        X.chain (by simp [previous, current])
      have hmiddle :
          (X.block previous).finalHole.externalDegree u =
            (X.block current).initialHole.externalDegree u :=
        (X.block previous).finalHole.externalDegree_eq_of_range_eq
          (X.block current).initialHole hchain
      calc
        (X.block ⟨n + 1, hn⟩).finalHole.externalDegree u =
            (X.block current).initialHole.externalDegree u := by
              simpa [current] using hblock
        _ = (X.block previous).finalHole.externalDegree u := hmiddle.symm
        _ = originalHole.externalDegree u := by
              simpa [previous] using ih hnPrevious

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

variable {families : PairingType → FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ObstructionSearchInitialization

variable {I : ObstructionSearchInitialization families Cprime}

namespace FiniteMixedSideOSExecution

/-- Target balance on the literal empty/nonempty execution split. -/
def TargetBalanced
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole) (u : V) : Prop :=
  match X with
  | .empty _ => True
  | .nonempty data => data.literal.trace.TargetBalanced u

/-- A positive target-balanced execution preserves the target's original-hole
external degree on the exact manuscript final hole. -/
theorem manuscriptFinalHole_externalDegree_eq_original_of_targetBalanced
    {source : I.Node} {originalHole : IndexedInducedHole G}
    (X : FiniteMixedSideOSExecution I source originalHole)
    (u : V) (hbalanced : X.TargetBalanced u)
    (hpos : 0 < X.toOrdered.blockCount) :
    X.toOrdered.manuscriptFinalHole.externalDegree u =
      originalHole.externalDegree u := by
  cases X with
  | empty hrun =>
      change 0 < 0 at hpos
      omega
  | nonempty data =>
      let last : Fin data.literal.trace.blockCount :=
        data.literal.trace.lastBlockIndex
      have hlast :=
        data.literal.trace.blockFinal_externalDegree_eq_original_through
          u hbalanced last.val last.isLt
      have hfinal :=
        data.toOrdered.manuscriptFinalHole_eq_lastBlockFinalHole hpos
      rw [hfinal]
      simpa [FiniteMixedSideOSExecution.toOrdered, last] using hlast

end FiniteMixedSideOSExecution

/-- A terminal stop whose target degree is generated by a literal
step-balanced finite execution.  The tether-link coordinates are the raw
Definition 19/20 stopping geometry used to derive flank adjacency. -/
structure FiniteMixedSideIncomingBalancedTerminalStopExecution
    (T : I.InitializationFiniteMixedSideTerminalCoreData)
    (C : FiniteMixedSideTerminalComponentExecution T target)
    (source target : I.Node)
    (incoming : I.graph.Arc source target) where
  targetBalanced :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.execution
      source).TargetBalanced (target : V)
  linkIndex :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      Fin (T.terminalPath target).card
  link_center_eq :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      (T.terminalPath target).vertex (linkIndex X) = X.center
  link_toward_target :
    ∀ X : FiniteMixedSideIncomingTerminalCloneWitness
        T source target incoming,
      match T.currentSlot source target with
      | .first =>
          (linkIndex X).val + 1 = (C.sameIndex C.targetCoordinate).val
      | .last =>
          (C.sameIndex C.targetCoordinate).val + 1 = (linkIndex X).val

namespace FiniteMixedSideIncomingBalancedTerminalStopExecution

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}
  {target source : I.Node}
  {incoming : I.graph.Arc source target}
  {C : FiniteMixedSideTerminalComponentExecution T target}

/-- The original-hole stopping clone has degree three, and target balance
transports that degree to the positive manuscript final hole. -/
theorem positive_finalDegree_three
    (E : FiniteMixedSideIncomingBalancedTerminalStopExecution
      T C source target incoming)
    (hclaw : G.IsClawFree)
    (hpos :
      0 <
        (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
          source).blockCount) :
    (T.execution.toInitializationFiniteMixedSideOSExecutionData.ordered
      source).manuscriptFinalHole.externalDegree (target : V) = 3 := by
  let Y := T.execution.toInitializationFiniteMixedSideOSExecutionData
  have htransport :=
    (Y.execution source).manuscriptFinalHole_externalDegree_eq_original_of_targetBalanced
      (target : V) E.targetBalanced hpos
  obtain ⟨i, hclone⟩ := T.exists_target_clone_of_incoming hclaw incoming
  have horiginal : Y.originalHole.externalDegree (target : V) = 3 :=
    hclone.externalDegree_eq_three
  exact htransport.trans horiginal

/-- Target balance and the raw tether link construct the operational tether
without assuming the terminal degree-three conclusion. -/
def toOperationalTether
    (E : FiniteMixedSideIncomingBalancedTerminalStopExecution
      T C source target incoming)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideIncomingOperationalTether T source target incoming where
  positive_finalDegree_three := E.positive_finalDegree_three hclaw
  clone_adj_flank := by
    intro X q
    let R : FiniteMixedSideIncomingTerminalStopExecution
        T C source target incoming :=
      { positive_target_clone := by
          intro hpos
          have hthree := E.positive_finalDegree_three hclaw hpos
          have houtside :=
            T.target_not_mem_manuscriptFinalHole_of_pos incoming hpos
          exact
            IndexedInducedHole.exists_singleVertexDeformation_of_externalDegree_eq_three
              _ hclaw houtside hthree
        linkIndex := E.linkIndex
        link_center_eq := E.link_center_eq
        link_toward_target := E.link_toward_target }
    exact R.toOperationalTether.clone_adj_flank X q

end FiniteMixedSideIncomingBalancedTerminalStopExecution

/-- Executable terminal events with target degree generated from the literal
`single`/`snoc` balance invariant. -/
structure InitializationFiniteMixedSideBalancedExecutableTerminalEvent
    (T : I.InitializationFiniteMixedSideTerminalCoreData) : Type (u + 1) where
  component : ∀ target : I.Node,
    FiniteMixedSideTerminalComponentExecution T target
  stop : ∀ ⦃source target : I.Node⦄
    (incoming : I.graph.Arc source target),
      FiniteMixedSideIncomingBalancedTerminalStopExecution
        T (component target) source target incoming

namespace InitializationFiniteMixedSideBalancedExecutableTerminalEvent

variable {T : I.InitializationFiniteMixedSideTerminalCoreData}

/-- All alternating-label, degree-three, and one-sided flank conclusions are
now theorems from raw component coordinates and the preserved target-balance
invariant. -/
def toLabelledOperationalTerminalData
    (E : InitializationFiniteMixedSideBalancedExecutableTerminalEvent T)
    (hclaw : G.IsClawFree) :
    FiniteMixedSideInitializationLabelledOperationalTerminalData T where
  labels := E.component.toAlternatingLabelData
  tether := fun incoming => (E.stop incoming).toOperationalTether hclaw

end InitializationFiniteMixedSideBalancedExecutableTerminalEvent

end ObstructionSearchInitialization
end FixedPairingPathFamily
end SimpleGraph
