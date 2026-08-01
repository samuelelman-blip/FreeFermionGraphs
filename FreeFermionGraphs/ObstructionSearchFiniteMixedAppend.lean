import FreeFermionGraphs.ObstructionSearchFiniteMixedBuild

/-!
# Concatenating finite Definition 19 executions

The literal obstruction search produces a finite sequence of nonempty path
blocks.  This module supplies the sequence operation needed after the
one-block constructor: two consecutive concrete deformations are concatenated
without changing either block's steps, and two complete Definition 19
deformations are concatenated when their intermediate hole carriers agree.

The two index embeddings below make the provenance of every flattened step
explicit.  No conclusion of Lemma 11 or Lemma 14 is assumed.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcreteDeformation

/-- Embed a step of the first deformation into a concatenated deformation. -/
def concatLeftIndex
    (A B : ConcreteDeformation O Cprime)
    (i : Fin A.stepCount) :
    Fin (A.stepCount + B.stepCount) :=
  ⟨i.val, by omega⟩

/-- Embed a step of the second deformation into a concatenated deformation. -/
def concatRightIndex
    (A B : ConcreteDeformation O Cprime)
    (i : Fin B.stepCount) :
    Fin (A.stepCount + B.stepCount) :=
  ⟨A.stepCount + i.val, by omega⟩

/-- Concatenate two nonempty concrete deformations whose intermediate hole
carriers agree. -/
def concat
    (A B : ConcreteDeformation O Cprime)
    (hA : 0 < A.stepCount)
    (hB : 0 < B.stepCount)
    (hboundary :
      Set.range
          (A.step ⟨A.stepCount - 1, by omega⟩).after.vertex =
        Set.range (B.step ⟨0, hB⟩).before.vertex) :
    ConcreteDeformation O Cprime where
  stepCount := A.stepCount + B.stepCount
  step := fun k =>
    if hk : k.val < A.stepCount then
      A.step ⟨k.val, hk⟩
    else
      B.step ⟨k.val - A.stepCount, by omega⟩
  carrier_chain := by
    intro i j hij
    by_cases hi : i.val < A.stepCount
    · by_cases hj : j.val < A.stepCount
      · rw [dif_pos hi, dif_pos hj]
        exact A.carrier_chain hij
      · rw [dif_pos hi, dif_neg hj]
        have hiLast : i.val = A.stepCount - 1 := by omega
        have hjFirst : j.val = A.stepCount := by omega
        have hiEq :
            (⟨i.val, hi⟩ : Fin A.stepCount) =
              ⟨A.stepCount - 1, by omega⟩ := by
          apply Fin.ext
          exact hiLast
        have hjEq :
            (⟨j.val - A.stepCount, by omega⟩ : Fin B.stepCount) =
              ⟨0, hB⟩ := by
          apply Fin.ext
          change j.val - A.stepCount = 0
          omega
        rw [hiEq, hjEq]
        exact hboundary
    · have hj : ¬j.val < A.stepCount := by omega
      rw [dif_neg hi, dif_neg hj]
      apply B.carrier_chain
      change (i.val - A.stepCount) + 1 =
        j.val - A.stepCount
      omega

@[simp] theorem concat_step_left
    (A B : ConcreteDeformation O Cprime)
    (hA : 0 < A.stepCount)
    (hB : 0 < B.stepCount)
    (hboundary :
      Set.range
          (A.step ⟨A.stepCount - 1, by omega⟩).after.vertex =
        Set.range (B.step ⟨0, hB⟩).before.vertex)
    (i : Fin A.stepCount) :
    (A.concat B hA hB hboundary).step
        (A.concatLeftIndex B i) = A.step i := by
  change (if hi : i.val < A.stepCount then
      A.step ⟨i.val, hi⟩
    else
      B.step ⟨i.val - A.stepCount, by omega⟩) = A.step i
  rw [dif_pos i.isLt]

@[simp] theorem concat_step_right
    (A B : ConcreteDeformation O Cprime)
    (hA : 0 < A.stepCount)
    (hB : 0 < B.stepCount)
    (hboundary :
      Set.range
          (A.step ⟨A.stepCount - 1, by omega⟩).after.vertex =
        Set.range (B.step ⟨0, hB⟩).before.vertex)
    (i : Fin B.stepCount) :
    (A.concat B hA hB hboundary).step
        (A.concatRightIndex B i) = B.step i := by
  change (if hi : A.stepCount + i.val < A.stepCount then
      A.step ⟨A.stepCount + i.val, hi⟩
    else
      B.step ⟨A.stepCount + i.val - A.stepCount, by omega⟩) =
        B.step i
  rw [dif_neg (by omega)]
  congr 1
  apply Fin.ext
  simp

end ConcreteDeformation

namespace FullDefinition19Deformation

/-- Concatenate two complete Definition 19 deformations.  Every successor
witness remains inside the block that supplied it. -/
def concat
    (A B : FullDefinition19Deformation O Cprime)
    (hboundary :
      Set.range A.terminalHole.vertex =
        Set.range B.initialHole.vertex) :
    FullDefinition19Deformation O Cprime := by
  have hchain :
      Set.range
          (A.deformation.step A.lastIndex).after.vertex =
        Set.range
          (B.deformation.step ⟨0, B.nonempty⟩).before.vertex := by
    simpa [terminalHole, initialHole] using hboundary
  refine {
    deformation := A.deformation.concat B.deformation
      A.nonempty B.nonempty hchain
    nonempty := by
      change 0 < A.deformation.stepCount + B.deformation.stepCount
      have hA := A.nonempty
      omega
    introduced_mem_prime := ?_
    removedPrime_hasSuccessor := ?_
  }
  · intro k
    by_cases hk : k.val < A.deformation.stepCount
    · let i : Fin A.deformation.stepCount := ⟨k.val, hk⟩
      have hkEq :
          k = A.deformation.concatLeftIndex B.deformation i := by
        apply Fin.ext
        rfl
      rw [hkEq]
      simpa only [ConcreteDeformation.concat_step_left] using
        A.introduced_mem_prime i
    · let i : Fin B.deformation.stepCount :=
        ⟨k.val - A.deformation.stepCount, by
          have hkLt := k.isLt
          change k.val < A.deformation.stepCount +
            B.deformation.stepCount at hkLt
          omega⟩
      have hkEq :
          k = A.deformation.concatRightIndex B.deformation i := by
        apply Fin.ext
        change k.val = A.deformation.stepCount +
          (k.val - A.deformation.stepCount)
        omega
      rw [hkEq]
      simpa only [ConcreteDeformation.concat_step_right] using
        B.introduced_mem_prime i
  · intro k hkPrime
    by_cases hk : k.val < A.deformation.stepCount
    · let i : Fin A.deformation.stepCount := ⟨k.val, hk⟩
      have hkEq :
          k = A.deformation.concatLeftIndex B.deformation i := by
        apply Fin.ext
        rfl
      rw [hkEq] at hkPrime ⊢
      have hstepI := ConcreteDeformation.concat_step_left
        A.deformation B.deformation A.nonempty B.nonempty hchain i
      have hiPrime :
          (A.deformation.step i).before.vertex
              (A.deformation.step i).removedIndex ∈ Cprime := by
        rw [hstepI] at hkPrime
        exact hkPrime
      obtain ⟨j, hij, hadj, hne, hnonadj⟩ :=
        A.removedPrime_hasSuccessor i hiPrime
      have hstepJ := ConcreteDeformation.concat_step_left
        A.deformation B.deformation A.nonempty B.nonempty hchain j
      refine ⟨A.deformation.concatLeftIndex B.deformation j,
        ?_, ?_, ?_, ?_⟩
      · exact hij
      · rw [hstepI, hstepJ]
        exact hadj
      · rw [hstepI, hstepJ]
        exact hne
      · rw [hstepI, hstepJ]
        exact hnonadj
    · let i : Fin B.deformation.stepCount :=
        ⟨k.val - A.deformation.stepCount, by
          have hkLt := k.isLt
          change k.val < A.deformation.stepCount +
            B.deformation.stepCount at hkLt
          omega⟩
      have hkEq :
          k = A.deformation.concatRightIndex B.deformation i := by
        apply Fin.ext
        change k.val = A.deformation.stepCount +
          (k.val - A.deformation.stepCount)
        omega
      rw [hkEq] at hkPrime ⊢
      have hstepI := ConcreteDeformation.concat_step_right
        A.deformation B.deformation A.nonempty B.nonempty hchain i
      have hiPrime :
          (B.deformation.step i).before.vertex
              (B.deformation.step i).removedIndex ∈ Cprime := by
        rw [hstepI] at hkPrime
        exact hkPrime
      obtain ⟨j, hij, hadj, hne, hnonadj⟩ :=
        B.removedPrime_hasSuccessor i hiPrime
      have hstepJ := ConcreteDeformation.concat_step_right
        A.deformation B.deformation A.nonempty B.nonempty hchain j
      refine ⟨A.deformation.concatRightIndex B.deformation j,
        ?_, ?_, ?_, ?_⟩
      · dsimp [ConcreteDeformation.concatRightIndex]
        omega
      · rw [hstepI, hstepJ]
        exact hadj
      · rw [hstepI, hstepJ]
        exact hne
      · rw [hstepI, hstepJ]
        exact hnonadj

/-- Search output obtained by concatenating two consecutive complete
Definition 19 executions. -/
def concatSearch
    (A B : FullDefinition19Deformation O Cprime)
    (hboundary :
      Set.range A.terminalHole.vertex =
        Set.range B.initialHole.vertex) :
    SearchDeformation O Cprime where
  run := some (A.concat B hboundary)

end FullDefinition19Deformation

end FixedPairingPathFamily

end SimpleGraph
