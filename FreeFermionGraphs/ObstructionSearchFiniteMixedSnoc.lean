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
  ⟨i.val, by omega⟩

/-- Index of the newly appended block. -/
def snocNewBlockIndex
    (X : FiniteMixedSideSearchTrace S originalHole) :
    Fin (X.blockCount + 1) :=
  ⟨X.blockCount, by omega⟩

/-- Block family after appending `D`. -/
def snocBlock
    (X : FiniteMixedSideSearchTrace S originalHole)
    (D : ConcretePathDeformation O Cprime)
    (i : Fin (X.blockCount + 1)) :
    ConcretePathDeformation O Cprime :=
  if hi : i.val < X.blockCount then
    X.block ⟨i.val, hi⟩
  else
    D

/-- Side tags after appending one block. -/
def snocSide
    (X : FiniteMixedSideSearchTrace S originalHole)
    (newSide : DeformationSide)
    (i : Fin (X.blockCount + 1)) :
    DeformationSide :=
  if hi : i.val < X.blockCount then
    X.side ⟨i.val, hi⟩
  else
    newSide

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
    (i : Fin (X.blockCount + 1))
    (s : Fin (X.snocBlock D i).deformation.stepCount) :
    Fin (X.snocFlattened D newSide F hchain).deformation.stepCount := by
  by_cases hi : i.val < X.blockCount
  · let old : Fin X.blockCount := ⟨i.val, hi⟩
    have hiEq : i = X.snocOldBlockIndex old := by
      apply Fin.ext
      rfl
    subst i
    let oldStep : Fin (X.block old).deformation.stepCount := by
      simpa using s
    exact X.flattened.deformation.concatLeftIndex
      (D.toFullDefinition19Deformation newSide F).deformation
      (X.stepIndex old oldStep)
  · have hiVal : i.val = X.blockCount := by
      have hiLt := i.isLt
      omega
    have hiEq : i = X.snocNewBlockIndex := by
      apply Fin.ext
      exact hiVal
    subst i
    let newStep : Fin D.deformation.stepCount := by
      simpa using s
    exact X.flattened.deformation.concatRightIndex
      (D.toFullDefinition19Deformation newSide F).deformation newStep

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
    by_cases hi : i.val < X.blockCount
    · let old : Fin X.blockCount := ⟨i.val, hi⟩
      have hiEq : i = X.snocOldBlockIndex old := by
        apply Fin.ext
        rfl
      subst i
      simpa using X.localData old
    · have hiVal : i.val = X.blockCount := by
        have hiLt := i.isLt
        omega
      have hiEq : i = X.snocNewBlockIndex := by
        apply Fin.ext
        exact hiVal
      subst i
      simpa using F
  chain := by
    intro i j hij
    by_cases hi : i.val < X.blockCount
    · by_cases hj : j.val < X.blockCount
      · let oldI : Fin X.blockCount := ⟨i.val, hi⟩
        let oldJ : Fin X.blockCount := ⟨j.val, hj⟩
        have hiEq : i = X.snocOldBlockIndex oldI := by
          apply Fin.ext
          rfl
        have hjEq : j = X.snocOldBlockIndex oldJ := by
          apply Fin.ext
          rfl
        subst i
        subst j
        exact X.chain hij
      · have hiVal : i.val = X.blockCount - 1 := by omega
        have hjVal : j.val = X.blockCount := by omega
        have hiEq : i = X.snocOldBlockIndex X.lastBlockIndex := by
          apply Fin.ext
          exact hiVal
        have hjEq : j = X.snocNewBlockIndex := by
          apply Fin.ext
          exact hjVal
        subst i
        subst j
        simpa using hchain
    · have hiVal : i.val = X.blockCount := by
        have hiLt := i.isLt
        omega
      have hjLt := j.isLt
      omega
  originalHole_eq := by
    simpa [snocBlock, X.blockCount_pos] using X.originalHole_eq
  removed_mem_original := by
    intro i s
    by_cases hi : i.val < X.blockCount
    · let old : Fin X.blockCount := ⟨i.val, hi⟩
      have hiEq : i = X.snocOldBlockIndex old := by
        apply Fin.ext
        rfl
      subst i
      simpa using X.removed_mem_original old s
    · have hiVal : i.val = X.blockCount := by
        have hiLt := i.isLt
        omega
      have hiEq : i = X.snocNewBlockIndex := by
        apply Fin.ext
        exact hiVal
      subst i
      simpa using hRemoved s
  path_pairwise := by
    intro i j hij
    by_cases hi : i.val < X.blockCount
    · let oldI : Fin X.blockCount := ⟨i.val, hi⟩
      have hiEq : i = X.snocOldBlockIndex oldI := by
        apply Fin.ext
        rfl
      subst i
      by_cases hj : j.val < X.blockCount
      · let oldJ : Fin X.blockCount := ⟨j.val, hj⟩
        have hjEq : j = X.snocOldBlockIndex oldJ := by
          apply Fin.ext
          rfl
        subst j
        apply X.path_pairwise
        intro hOld
        apply hij
        rw [hOld]
      · have hjVal : j.val = X.blockCount := by
          have hjLt := j.isLt
          omega
        have hjEq : j = X.snocNewBlockIndex := by
          apply Fin.ext
          exact hjVal
        subst j
        simpa using hFresh oldI
    · have hiVal : i.val = X.blockCount := by
        have hiLt := i.isLt
        omega
      have hiEq : i = X.snocNewBlockIndex := by
        apply Fin.ext
        exact hiVal
      subst i
      by_cases hj : j.val < X.blockCount
      · let oldJ : Fin X.blockCount := ⟨j.val, hj⟩
        have hjEq : j = X.snocOldBlockIndex oldJ := by
          apply Fin.ext
          rfl
        subst j
        intro hEq
        exact hFresh oldJ hEq.symm
      · have hjVal : j.val = X.blockCount := by
          have hjLt := j.isLt
          omega
        exfalso
        apply hij
        apply Fin.ext
        exact hjVal.symm
  firstIntroduced_uniquePath := by
    intro i
    by_cases hi : i.val < X.blockCount
    · let old : Fin X.blockCount := ⟨i.val, hi⟩
      have hiEq : i = X.snocOldBlockIndex old := by
        apply Fin.ext
        rfl
      subst i
      simpa using X.firstIntroduced_uniquePath old
    · have hiVal : i.val = X.blockCount := by
        have hiLt := i.isLt
        omega
      have hiEq : i = X.snocNewBlockIndex := by
        apply Fin.ext
        exact hiVal
      subst i
      simpa using hUnique
  stepIndex := X.snocStepIndex D newSide F hchain
  step_eq := by
    intro i s
    by_cases hi : i.val < X.blockCount
    · let old : Fin X.blockCount := ⟨i.val, hi⟩
      have hiEq : i = X.snocOldBlockIndex old := by
        apply Fin.ext
        rfl
      subst i
      let oldStep : Fin (X.block old).deformation.stepCount := by
        simpa using s
      change
        (X.snocFlattened D newSide F hchain).deformation.step
            (X.flattened.deformation.concatLeftIndex
              (D.toFullDefinition19Deformation newSide F).deformation
              (X.stepIndex old oldStep)) =
          (X.block old).deformation.step oldStep
      rw [FullDefinition19Deformation.concat_deformation_step_left]
      exact X.step_eq old oldStep
    · have hiVal : i.val = X.blockCount := by
        have hiLt := i.isLt
        omega
      have hiEq : i = X.snocNewBlockIndex := by
        apply Fin.ext
        exact hiVal
      subst i
      let newStep : Fin D.deformation.stepCount := by
        simpa using s
      change
        (X.snocFlattened D newSide F hchain).deformation.step
            (X.flattened.deformation.concatRightIndex
              (D.toFullDefinition19Deformation newSide F).deformation
              newStep) =
          D.deformation.step newStep
      rw [FullDefinition19Deformation.concat_deformation_step_right]
      rfl
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
      change (X.stepIndex i s).val = k.val
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
      change X.flattened.deformation.stepCount + s.val = k.val
      dsimp [s]
      omega
  stepIndex_order := by
    intro i j s t horder
    by_cases hi : i.val < X.blockCount
    · let oldI : Fin X.blockCount := ⟨i.val, hi⟩
      have hiEq : i = X.snocOldBlockIndex oldI := by
        apply Fin.ext
        rfl
      subst i
      let oldS : Fin (X.block oldI).deformation.stepCount := by
        simpa using s
      by_cases hj : j.val < X.blockCount
      · let oldJ : Fin X.blockCount := ⟨j.val, hj⟩
        have hjEq : j = X.snocOldBlockIndex oldJ := by
          apply Fin.ext
          rfl
        subst j
        let oldT : Fin (X.block oldJ).deformation.stepCount := by
          simpa using t
        change (X.stepIndex oldI oldS).val <
          (X.stepIndex oldJ oldT).val
        apply X.stepIndex_order
        simpa [snocOldBlockIndex] using horder
      · have hjVal : j.val = X.blockCount := by
          have hjLt := j.isLt
          omega
        have hjEq : j = X.snocNewBlockIndex := by
          apply Fin.ext
          exact hjVal
        subst j
        let newT : Fin D.deformation.stepCount := by
          simpa using t
        change (X.stepIndex oldI oldS).val <
          X.flattened.deformation.stepCount + newT.val
        have hleft := (X.stepIndex oldI oldS).isLt
        omega
    · have hiVal : i.val = X.blockCount := by
        have hiLt := i.isLt
        omega
      have hiEq : i = X.snocNewBlockIndex := by
        apply Fin.ext
        exact hiVal
      subst i
      have hjVal : j.val = X.blockCount := by
        rcases horder with hij | ⟨hij, _hst⟩
        · have hjLt := j.isLt
          omega
        · exact hij.symm
      have hjEq : j = X.snocNewBlockIndex := by
        apply Fin.ext
        exact hjVal
      subst j
      let newS : Fin D.deformation.stepCount := by
        simpa using s
      let newT : Fin D.deformation.stepCount := by
        simpa using t
      change X.flattened.deformation.stepCount + newS.val <
        X.flattened.deformation.stepCount + newT.val
      rcases horder with hij | ⟨_hij, hst⟩
      · omega
      · exact Nat.add_lt_add_left hst _

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
