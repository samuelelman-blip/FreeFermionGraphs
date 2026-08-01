import FreeFermionGraphs.ObstructionSearchFiniteMixedAppend

/-!
# Terminal-step provenance for finite mixed traces

The ordered, surjective local-to-flattened step map sends the final step of
the final path block to the final step of the flattened Definition 19 run.
Consequently the flattened terminal hole has exactly the carrier of the last
block's final hole.  This is the boundary fact needed to append the next
literal obstruction-search block without accepting a second flattened-chain
premise.
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

/-- Index of the final path block in a nonempty finite trace. -/
def lastBlockIndex
    (X : FiniteMixedSideSearchTrace S originalHole) :
    Fin X.blockCount :=
  ⟨X.blockCount - 1, by
    have hpos := X.blockCount_pos
    omega⟩

/-- The final local replacement in the final path block. -/
def lastLocalStepIndex
    (X : FiniteMixedSideSearchTrace S originalHole) :
    Fin (X.block X.lastBlockIndex).deformation.stepCount :=
  (X.block X.lastBlockIndex).lastIndex

/-- The final local block step is the final flattened execution step. -/
theorem stepIndex_last_eq
    (X : FiniteMixedSideSearchTrace S originalHole) :
    X.stepIndex X.lastBlockIndex X.lastLocalStepIndex =
      X.flattened.lastIndex := by
  obtain ⟨i, s, his⟩ :=
    X.stepIndex_surjective X.flattened.lastIndex
  have hiLe : i.val ≤ X.lastBlockIndex.val := by
    dsimp [lastBlockIndex]
    have hiLt := i.isLt
    omega
  by_cases hi : i.val < X.lastBlockIndex.val
  · have horder := X.stepIndex_order i X.lastBlockIndex
      s X.lastLocalStepIndex (Or.inl hi)
    rw [his] at horder
    have hlastVal : X.flattened.lastIndex.val =
        X.flattened.deformation.stepCount - 1 := rfl
    have htargetLt :=
      (X.stepIndex X.lastBlockIndex X.lastLocalStepIndex).isLt
    omega
  · have hiVal : i.val = X.lastBlockIndex.val := by omega
    have hiEq : i = X.lastBlockIndex := by
      apply Fin.ext
      exact hiVal
    subst i
    have hsLe : s.val ≤ X.lastLocalStepIndex.val := by
      dsimp [lastLocalStepIndex, ConcretePathDeformation.lastIndex]
      have hsLt := s.isLt
      omega
    by_cases hs : s.val < X.lastLocalStepIndex.val
    · have horder := X.stepIndex_order X.lastBlockIndex
        X.lastBlockIndex s X.lastLocalStepIndex
        (Or.inr ⟨rfl, hs⟩)
      rw [his] at horder
      have hlastVal : X.flattened.lastIndex.val =
          X.flattened.deformation.stepCount - 1 := rfl
      have htargetLt :=
        (X.stepIndex X.lastBlockIndex X.lastLocalStepIndex).isLt
      omega
    · have hsVal : s.val = X.lastLocalStepIndex.val := by omega
      have hsEq : s = X.lastLocalStepIndex := by
        apply Fin.ext
        exact hsVal
      subst s
      exact his

/-- The terminal flattened hole and the last literal path block have the same
vertex carrier. -/
theorem terminalHole_range_eq_lastBlock_finalHole
    (X : FiniteMixedSideSearchTrace S originalHole) :
    Set.range X.flattened.terminalHole.vertex =
      Set.range (X.block X.lastBlockIndex).finalHole.vertex := by
  change
    Set.range
        (X.flattened.deformation.step X.flattened.lastIndex).after.vertex =
      Set.range
        ((X.block X.lastBlockIndex).deformation.step
          X.lastLocalStepIndex).after.vertex
  rw [← X.stepIndex_last_eq]
  rw [X.step_eq]

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
