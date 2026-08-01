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
      X.flattened.deformation.concatRightIndex
        (D.toFullDefinition19Deformation newSide F).deformation
        (by simpa [snocBlock] using s))
    (fun old s =>
      X.flattened.deformation.concatLeftIndex
        (D.toFullDefinition19Deformation newSide F).deformation
        (X.stepIndex old (by simpa [snocBlock] using s)))
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
  localData := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [snocBlock, snocSide] using F
    · intro old
      simpa [snocBlock, snocSide] using X.localData old
  chain := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · intro j hij
      have hjLt := j.isLt
      omega
    · intro oldI
      intro j
      refine Fin.lastCases ?_ ?_ j
      · intro hij
        have hlast : oldI = X.lastBlockIndex := by
          apply Fin.ext
          dsimp [snocOldBlockIndex, snocNewBlockIndex,
            lastBlockIndex] at hij ⊢
          omega
        rw [hlast]
        simpa [snocBlock] using hchain
      · intro oldJ hij
        simpa [snocBlock, snocOldBlockIndex] using X.chain hij
  originalHole_eq := by
    have hzero :
        (⟨0, by omega⟩ : Fin (X.blockCount + 1)) =
          X.snocOldBlockIndex X.firstIndex := by
      apply Fin.ext
      rfl
    rw [hzero]
    simpa [firstIndex] using X.originalHole_eq
  removed_mem_original := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · intro s
      let newStep : Fin D.deformation.stepCount := by
        simpa [snocBlock] using s
      simpa [snocBlock] using hRemoved newStep
    · intro old s
      let oldStep : Fin (X.block old).deformation.stepCount := by
        simpa [snocBlock] using s
      simpa [snocBlock] using X.removed_mem_original old oldStep
  path_pairwise := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · intro hij
        exact (hij rfl).elim
      · intro oldJ hij hEq
        exact hFresh oldJ hEq.symm
    · intro oldI
      intro j
      refine Fin.lastCases ?_ ?_ j
      · intro _hij
        simpa [snocBlock] using hFresh oldI
      · intro oldJ hij
        apply X.path_pairwise
        intro hOld
        apply hij
        cases hOld
        rfl
  firstIntroduced_uniquePath := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [snocBlock] using hUnique
    · intro old
      simpa [snocBlock] using X.firstIntroduced_uniquePath old
  stepIndex := X.snocStepIndex D newSide F hchain
  step_eq := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · intro s
      let newStep : Fin D.deformation.stepCount := by
        simpa [snocBlock] using s
      have hmap :
          X.snocStepIndex D newSide F hchain X.snocNewBlockIndex s =
            X.flattened.deformation.concatRightIndex
              (D.toFullDefinition19Deformation newSide F).deformation
              newStep := by
        simp [snocStepIndex, snocNewBlockIndex, snocBlock, newStep]
      rw [hmap]
      rw [FullDefinition19Deformation.concat_deformation_step_right]
      simpa [snocBlock] using congrArg D.deformation.step
        (Fin.ext (show newStep.val = s.val by rfl))
    · intro old s
      let oldStep : Fin (X.block old).deformation.stepCount := by
        simpa [snocBlock] using s
      have hmap :
          X.snocStepIndex D newSide F hchain
              (X.snocOldBlockIndex old) s =
            X.flattened.deformation.concatLeftIndex
              (D.toFullDefinition19Deformation newSide F).deformation
              (X.stepIndex old oldStep) := by
        simp [snocStepIndex, snocOldBlockIndex, snocBlock, oldStep]
      rw [hmap]
      rw [FullDefinition19Deformation.concat_deformation_step_left]
      simpa [snocBlock] using X.step_eq old oldStep
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
      simp [snocStepIndex, newI, snocOldBlockIndex, snocBlock, newS]
      exact congrArg Fin.val his
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
      simp [snocStepIndex, snocNewBlockIndex, snocBlock, newS]
      change X.flattened.deformation.stepCount + s.val = k.val
      dsimp [s]
      omega
  stepIndex_order := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · intro s t horder
        let newS : Fin D.deformation.stepCount := by
          simpa [snocBlock] using s
        let newT : Fin D.deformation.stepCount := by
          simpa [snocBlock] using t
        simp [snocStepIndex, snocNewBlockIndex, snocBlock, newS, newT]
        rcases horder with hij | ⟨_hij, hst⟩
        · omega
        · exact Nat.add_lt_add_left hst _
      · intro oldJ s t horder
        exfalso
        rcases horder with hij | ⟨hij, _hst⟩ <;>
          simp [snocNewBlockIndex, snocOldBlockIndex] at hij
    · intro oldI
      intro j
      refine Fin.lastCases ?_ ?_ j
      · intro s t horder
        let oldS : Fin (X.block oldI).deformation.stepCount := by
          simpa [snocBlock] using s
        let newT : Fin D.deformation.stepCount := by
          simpa [snocBlock] using t
        simp [snocStepIndex, snocOldBlockIndex, snocNewBlockIndex,
          snocBlock, oldS, newT]
        have hleft := (X.stepIndex oldI oldS).isLt
        omega
      · intro oldJ s t horder
        let oldS : Fin (X.block oldI).deformation.stepCount := by
          simpa [snocBlock] using s
        let oldT : Fin (X.block oldJ).deformation.stepCount := by
          simpa [snocBlock] using t
        simp [snocStepIndex, snocOldBlockIndex, snocBlock, oldS, oldT]
        apply X.stepIndex_order
        simpa [snocOldBlockIndex] using horder

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
