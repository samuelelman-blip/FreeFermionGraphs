import FreeFermionGraphs.ObstructionSearchFiniteMixedLastStep

/-!
# Appending a literal block to a finite mixed trace

This is the inductive constructor following the one-block base case.  Given a
finite trace and the next Definition 19 path block, it derives the flattened
terminal boundary from terminal-step provenance, concatenates the complete
deformations, and extends every block and step provenance field.

The constructor requires only the new block's literal execution invariants:
its carrier chain from the previous block, original-hole removal membership,
path freshness, and unique first-introduced path.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace FullDefinition19Deformation

@[simp] theorem concat_deformation_step_left
    (A B : FullDefinition19Deformation O Cprime)
    (hboundary :
      Set.range A.terminalHole.vertex =
        Set.range B.initialHole.vertex)
    (i : Fin A.deformation.stepCount) :
    (A.concat B hboundary).deformation.step
        (A.deformation.concatLeftIndex B.deformation i) =
      A.deformation.step i := by
  unfold concat
  simp

@[simp] theorem concat_deformation_step_right
    (A B : FullDefinition19Deformation O Cprime)
    (hboundary :
      Set.range A.terminalHole.vertex =
        Set.range B.initialHole.vertex)
    (i : Fin B.deformation.stepCount) :
    (A.concat B hboundary).deformation.step
        (A.deformation.concatRightIndex B.deformation i) =
      B.deformation.step i := by
  unfold concat
  simp

end FullDefinition19Deformation

namespace ConcretePathDeformation

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Embed an existing block index into a trace extended by one block. -/
def snocOldBlockIndex
    (X : FiniteMixedSideSearchTrace S originalHole)
    (i : Fin X.blockCount) :
    Fin (X.blockCount + 1) :=
  Fin.castSucc i

/-- Index of the newly appended block. -/
def snocNewBlockIndex
    (X : FiniteMixedSideSearchTrace S originalHole) :
    Fin (X.blockCount + 1) :=
  Fin.last X.blockCount

/-- Block family after appending `D`, defined by the dependent last-element
eliminator for `Fin (n + 1)`. -/
def snocBlock
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (i : Fin (X.blockCount + 1)) :
    ConcretePathDeformation O Cprime :=
  Fin.lastCases D (fun old => X.block old) i

/-- Side tags after appending one block. -/
def snocSide
    (X : FiniteMixedSideSearchTrace S originalHole)
    (newSide : DeformationSide)
    (i : Fin (X.blockCount + 1)) :
    DeformationSide :=
  Fin.lastCases newSide (fun old => X.side old) i

@[simp] theorem snocBlock_old
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (i : Fin X.blockCount) :
    X.snocBlock D (X.snocOldBlockIndex i) = X.block i := by
  simp [snocBlock, snocOldBlockIndex]

@[simp] theorem snocBlock_new
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime) :
    X.snocBlock D X.snocNewBlockIndex = D := by
  simp [snocBlock, snocNewBlockIndex]

@[simp] theorem snocSide_old
    (X : FiniteMixedSideSearchTrace S originalHole)
    (newSide : DeformationSide)
    (i : Fin X.blockCount) :
    X.snocSide newSide (X.snocOldBlockIndex i) = X.side i := by
  simp [snocSide, snocOldBlockIndex]

@[simp] theorem snocSide_new
    (X : FiniteMixedSideSearchTrace S originalHole)
    (newSide : DeformationSide) :
    X.snocSide newSide X.snocNewBlockIndex = newSide := by
  simp [snocSide, snocNewBlockIndex]

/-- The block chain supplies the terminal boundary for flattened
concatenation. -/
theorem snoc_flattened_boundary
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (newSide : DeformationSide)
    (F : (D.reorient newSide).FullDefinition19Lemma11AData)
    (hchain :
      Set.range (X.block X.lastBlockIndex).finalHole.vertex =
        Set.range D.initialHole.vertex) :
    Set.range X.flattened.terminalHole.vertex =
      Set.range (D.toFullDefinition19Deformation newSide F).initialHole.vertex := by
  calc
    Set.range X.flattened.terminalHole.vertex =
        Set.range (X.block X.lastBlockIndex).finalHole.vertex :=
      X.terminalHole_range_eq_lastBlock_finalHole
    _ = Set.range D.initialHole.vertex := hchain
    _ = Set.range
        (D.toFullDefinition19Deformation newSide F).initialHole.vertex := rfl

/-- Flattened complete deformation after appending one literal block. -/
def snocFlattened
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (newSide : DeformationSide)
    (F : (D.reorient newSide).FullDefinition19Lemma11AData)
    (hchain :
      Set.range (X.block X.lastBlockIndex).finalHole.vertex =
        Set.range D.initialHole.vertex) :
    FullDefinition19Deformation O Cprime :=
  X.flattened.concat (D.toFullDefinition19Deformation newSide F)
    (X.snoc_flattened_boundary D newSide F hchain)

/-- Search output after appending one literal block. -/
def snocSearch
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (newSide : DeformationSide)
    (F : (D.reorient newSide).FullDefinition19Lemma11AData)
    (hchain :
      Set.range (X.block X.lastBlockIndex).finalHole.vertex =
        Set.range D.initialHole.vertex) :
    SearchDeformation O Cprime where
  run := some (X.snocFlattened D newSide F hchain)

/-- Local-to-flattened step map after appending one block. -/
def snocStepIndex
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (newSide : DeformationSide)
    (F : (D.reorient newSide).FullDefinition19Lemma11AData)
    (hchain :
      Set.range (X.block X.lastBlockIndex).finalHole.vertex =
        Set.range D.initialHole.vertex)
    (i : Fin (X.blockCount + 1)) :
    Fin (X.snocBlock D i).deformation.stepCount →
      Fin (X.snocFlattened D newSide F hchain).deformation.stepCount :=
  Fin.lastCases
    (fun s =>
      let newStep : Fin D.deformation.stepCount :=
        Fin.cast (by rw [snocBlock_new]) s
      let fullStep : Fin
          (D.toFullDefinition19Deformation newSide F).deformation.stepCount :=
        Fin.cast (by rfl) newStep
      X.flattened.deformation.concatRightIndex
        (D.toFullDefinition19Deformation newSide F).deformation
        fullStep)
    (fun old s =>
      let oldStep : Fin (X.block old).deformation.stepCount :=
        Fin.cast (by rw [snocBlock_old]) s
      X.flattened.deformation.concatLeftIndex
        (D.toFullDefinition19Deformation newSide F).deformation
        (X.stepIndex old oldStep))
    i

/-- Append one literal Definition 19 path block to an existing finite trace. -/
def snoc
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (newSide : DeformationSide)
    (F : (D.reorient newSide).FullDefinition19Lemma11AData)
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
      (Set.range D.path.vertex)) :
    FiniteMixedSideSearchTrace
      (X.snocSearch D newSide F hchain) originalHole where
  flattened := X.snocFlattened D newSide F hchain
  run_eq := rfl
  blockCount := X.blockCount + 1
  blockCount_pos := by omega
  block := X.snocBlock D
  side := X.snocSide newSide
  localData := Fin.lastCases
    (by simpa only [snocBlock_new, snocSide_new] using F)
    (fun old => by
      simpa only [snocBlock_old, snocSide_old] using X.localData old)
  chain := by
    intro i j hij
    exact Fin.lastCases
      (motive := fun i => i.val + 1 = j.val →
        Set.range (X.snocBlock D i).finalHole.vertex =
          Set.range (X.snocBlock D j).initialHole.vertex)
      (by
        intro h
        have hjLt := j.isLt
        omega)
      (fun oldI => by
        intro h
        exact Fin.lastCases
          (motive := fun j => oldI.val + 1 = j.val →
            Set.range (X.snocBlock D (Fin.castSucc oldI)).finalHole.vertex =
              Set.range (X.snocBlock D j).initialHole.vertex)
          (by
            intro holdLast
            have hlast : oldI = X.lastBlockIndex := by
              apply Fin.ext
              dsimp [lastBlockIndex] at holdLast ⊢
              omega
            rw [snocBlock_old, snocBlock_new, hlast]
            exact hchain)
          (fun oldJ => by
            intro hold
            rw [snocBlock_old, snocBlock_old]
            exact X.chain hold)
          j h)
      i hij
  originalHole_eq := by
    have hzero :
        (⟨0, by omega⟩ : Fin (X.blockCount + 1)) =
          X.snocOldBlockIndex X.firstIndex := by
      apply Fin.ext
      rfl
    rw [hzero]
    rw [snocBlock_old]
    simpa [firstIndex] using X.originalHole_eq
  removed_mem_original := by
    intro i
    exact Fin.lastCases
      (motive := fun i => ∀ s : Fin (X.snocBlock D i).deformation.stepCount,
        ((X.snocBlock D i).deformation.step s).before.vertex
            ((X.snocBlock D i).deformation.step s).removedIndex ∈
          Set.range originalHole.vertex)
      (by
        intro s
        rw [snocBlock_new] at s ⊢
        exact hRemoved s)
      (fun old => by
        intro s
        rw [snocBlock_old] at s ⊢
        exact X.removed_mem_original old s)
      i
  path_pairwise := by
    intro i j hij
    exact Fin.lastCases
      (motive := fun i => i ≠ j →
        Set.range (X.snocBlock D i).path.vertex ≠
          Set.range (X.snocBlock D j).path.vertex)
      (by
        intro hne
        exact Fin.lastCases
          (motive := fun j => Fin.last X.blockCount ≠ j →
            Set.range (X.snocBlock D (Fin.last X.blockCount)).path.vertex ≠
              Set.range (X.snocBlock D j).path.vertex)
          (by intro h; exact (h rfl).elim)
          (fun oldJ => by
            intro _h hEq
            rw [snocBlock_new, snocBlock_old] at hEq
            exact hFresh oldJ hEq.symm)
          j hne)
      (fun oldI => by
        intro hne
        exact Fin.lastCases
          (motive := fun j => Fin.castSucc oldI ≠ j →
            Set.range (X.snocBlock D (Fin.castSucc oldI)).path.vertex ≠
              Set.range (X.snocBlock D j).path.vertex)
          (by
            intro _h
            rw [snocBlock_old, snocBlock_new]
            exact hFresh oldI)
          (fun oldJ => by
            intro hcast
            rw [snocBlock_old, snocBlock_old]
            apply X.path_pairwise
            intro hold
            apply hcast
            cases hold
            rfl)
          j hne)
      i hij
  firstIntroduced_uniquePath := by
    intro i
    exact Fin.lastCases
      (by rw [snocBlock_new]; exact hUnique)
      (fun old => by
        rw [snocBlock_old]
        exact X.firstIntroduced_uniquePath old)
      i
  stepIndex := X.snocStepIndex D newSide F hchain
  step_eq := by
    intro i
    exact Fin.lastCases
      (motive := fun i => ∀ s : Fin (X.snocBlock D i).deformation.stepCount,
        (X.snocFlattened D newSide F hchain).deformation.step
            (X.snocStepIndex D newSide F hchain i s) =
          (X.snocBlock D i).deformation.step s)
      (by
        intro s
        rw [snocBlock_new] at s ⊢
        simp [snocStepIndex, snocFlattened,
          FullDefinition19Deformation.concat_deformation_step_right])
      (fun old => by
        intro s
        rw [snocBlock_old] at s ⊢
        simpa [snocStepIndex, snocFlattened] using X.step_eq old s)
      i
  stepIndex_surjective := by
    intro k
    by_cases hk : k.val < X.flattened.deformation.stepCount
    · let oldK : Fin X.flattened.deformation.stepCount := ⟨k.val, hk⟩
      obtain ⟨i, s, his⟩ := X.stepIndex_surjective oldK
      let newI := X.snocOldBlockIndex i
      let newS : Fin (X.snocBlock D newI).deformation.stepCount := by
        simpa [newI] using s
      refine ⟨newI, newS, ?_⟩
      apply Fin.ext
      simpa [snocStepIndex, newI, newS,
        ConcreteDeformation.concatLeftIndex] using congrArg Fin.val his
    · have hkLt := k.isLt
      change k.val < X.flattened.deformation.stepCount +
        D.deformation.stepCount at hkLt
      let s : Fin D.deformation.stepCount :=
        ⟨k.val - X.flattened.deformation.stepCount, by omega⟩
      let newS : Fin
          (X.snocBlock D X.snocNewBlockIndex).deformation.stepCount := by
        simpa using s
      refine ⟨X.snocNewBlockIndex, newS, ?_⟩
      apply Fin.ext
      simp [snocStepIndex, snocNewBlockIndex, newS,
        ConcreteDeformation.concatRightIndex]
      dsimp [s, newS]
      omega
  stepIndex_order := by
    intro i
    exact Fin.lastCases
      (motive := fun i => ∀ (j : Fin (X.blockCount + 1))
          (s : Fin (X.snocBlock D i).deformation.stepCount)
          (t : Fin (X.snocBlock D j).deformation.stepCount),
        (i.val < j.val ∨ (i.val = j.val ∧ s.val < t.val)) →
          (X.snocStepIndex D newSide F hchain i s).val <
            (X.snocStepIndex D newSide F hchain j t).val)
      (by
        intro j
        exact Fin.lastCases
          (motive := fun j => ∀
              (s : Fin (X.snocBlock D (Fin.last X.blockCount)).deformation.stepCount)
              (t : Fin (X.snocBlock D j).deformation.stepCount),
            ((Fin.last X.blockCount).val < j.val ∨
              ((Fin.last X.blockCount).val = j.val ∧ s.val < t.val)) →
              (X.snocStepIndex D newSide F hchain
                  (Fin.last X.blockCount) s).val <
                (X.snocStepIndex D newSide F hchain j t).val)
          (by
            intro s t horder
            rw [snocBlock_new] at s t
            simp [snocStepIndex, ConcreteDeformation.concatRightIndex]
            rcases horder with hij | ⟨_hij, hst⟩
            · omega
            · exact Nat.add_lt_add_left hst _)
          (fun oldJ => by
            intro s t horder
            exfalso
            have hJ := oldJ.isLt
            rcases horder with hij | ⟨hij, _hst⟩ <;> omega)
          j)
      (fun oldI => by
        intro j
        exact Fin.lastCases
          (motive := fun j => ∀
              (s : Fin (X.snocBlock D (Fin.castSucc oldI)).deformation.stepCount)
              (t : Fin (X.snocBlock D j).deformation.stepCount),
            ((Fin.castSucc oldI).val < j.val ∨
              ((Fin.castSucc oldI).val = j.val ∧ s.val < t.val)) →
              (X.snocStepIndex D newSide F hchain
                  (Fin.castSucc oldI) s).val <
                (X.snocStepIndex D newSide F hchain j t).val)
          (by
            intro s t _horder
            rw [snocBlock_old] at s
            rw [snocBlock_new] at t
            simp [snocStepIndex, ConcreteDeformation.concatLeftIndex,
              ConcreteDeformation.concatRightIndex]
            have hleft := (X.stepIndex oldI s).isLt
            omega)
          (fun oldJ => by
            intro s t horder
            rw [snocBlock_old] at s t
            simp [snocStepIndex, ConcreteDeformation.concatLeftIndex]
            apply X.stepIndex_order
            exact horder)
          j)
      i

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
