import FreeFermionGraphs.ObstructionSearchFiniteMixedTrace

/-!
# Bounded mixed-side Definition 19 prefixes

The manuscript's Definition 19 history preceding a current path block has
exactly `r` blocks when the current block has index `r`.  It is not a total
sequence indexed by every natural number.

This module gives that bounded history its own interface and constructs it
canonically from `FiniteMixedSideSearchTrace`.  The interface retains the
local data used by the existing Lemma 11(a) proof: the mixed side of every
block, carrier links, distinct paths, Corollary 10 endpoint uniqueness, and
membership of the current removed vertices in the fixed original hole.

No infinite tail is invented, and no conclusion of Lemma 11 or Lemma 14 is
stored as a field.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
  {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- The genuinely finite positive Definition 19 history preceding one current
mixed-side path block.

`priorBlock` is indexed by `Fin priorCount`, so the structure asks for no data
beyond the literal earlier prefix. -/
structure FiniteMixedSideLemma11AHistoryData
    (D : ConcretePathDeformation O Cprime)
    (originalHole : IndexedInducedHole G) where
  currentSide : DeformationSide
  current : (D.reorient currentSide).FullDefinition19Lemma11AData
  priorCount : Nat
  priorCount_pos : 0 < priorCount
  priorBlock : Fin priorCount → ConcretePathDeformation O Cprime
  priorSide : Fin priorCount → DeformationSide
  priorData : ∀ r : Fin priorCount,
    ((priorBlock r).reorient (priorSide r)).FullDefinition19Lemma11AData
  priorChain : ∀ {r q : Fin priorCount}, r.val + 1 = q.val →
    Set.range (priorBlock r).finalHole.vertex =
      Set.range (priorBlock q).initialHole.vertex
  firstInitial_eq_original :
    Set.range
        (priorBlock ⟨0, priorCount_pos⟩).initialHole.vertex =
      Set.range originalHole.vertex
  lastFinal_eq_current : ∀ r : Fin priorCount,
    r.val + 1 = priorCount →
      Set.range (priorBlock r).finalHole.vertex =
        Set.range D.initialHole.vertex
  priorPath_ne_current : ∀ r : Fin priorCount,
    Set.range (priorBlock r).path.vertex ≠ Set.range D.path.vertex
  priorPath_pairwise : ∀ {r q : Fin priorCount}, r ≠ q →
    Set.range (priorBlock r).path.vertex ≠
      Set.range (priorBlock q).path.vertex
  earlierFirstIntroduced_uniquePath : ∀ r : Fin priorCount,
    O.IsUniqueContainingPath
      ((priorBlock r).deformation.step
        (priorBlock r).firstIndex).introduced
      (Set.range (priorBlock r).path.vertex)
  currentRemoved_mem_original :
    ∀ s : Fin D.deformation.stepCount,
      (D.deformation.step s).before.vertex
          (D.deformation.step s).removedIndex ∈
        Set.range originalHole.vertex

namespace FiniteMixedSideLemma11AHistoryData

variable {D : ConcretePathDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- The last index of a nonempty finite positive history. -/
def lastIndex
    (H : FiniteMixedSideLemma11AHistoryData D originalHole) :
    Fin H.priorCount :=
  ⟨H.priorCount - 1, by
    have hpos := H.priorCount_pos
    omega⟩

/-- The final carrier of the bounded prefix is the initial carrier of the
current block. -/
theorem lastFinal_eq_current'
    (H : FiniteMixedSideLemma11AHistoryData D originalHole) :
    Set.range (H.priorBlock H.lastIndex).finalHole.vertex =
      Set.range D.initialHole.vertex := by
  apply H.lastFinal_eq_current
  change H.priorCount - 1 + 1 = H.priorCount
  have hpos := H.priorCount_pos
  omega

end FiniteMixedSideLemma11AHistoryData

namespace FiniteMixedSideSearchTrace

variable {S : SearchDeformation O Cprime}
  {originalHole : IndexedInducedHole G}

/-- Embed an index from the strict prefix before `current` into the full
finite trace. -/
def priorIndex
    (X : FiniteMixedSideSearchTrace S originalHole)
    (current : Fin X.blockCount)
    (r : Fin current.val) : Fin X.blockCount :=
  ⟨r.val, lt_trans r.isLt current.isLt⟩

@[simp] theorem priorIndex_val
    (X : FiniteMixedSideSearchTrace S originalHole)
    (current : Fin X.blockCount)
    (r : Fin current.val) :
    (X.priorIndex current r).val = r.val :=
  rfl

/-- Every noninitial trace block canonically carries exactly its finite earlier
Definition 19 prefix. -/
def finiteHistoryAt
    (X : FiniteMixedSideSearchTrace S originalHole)
    (current : Fin X.blockCount)
    (hcurrent : 0 < current.val) :
    FiniteMixedSideLemma11AHistoryData
      (X.block current) originalHole where
  currentSide := X.side current
  current := X.localData current
  priorCount := current.val
  priorCount_pos := hcurrent
  priorBlock := fun r => X.block (X.priorIndex current r)
  priorSide := fun r => X.side (X.priorIndex current r)
  priorData := fun r => X.localData (X.priorIndex current r)
  priorChain := by
    intro r q hrq
    exact X.chain
      (i := X.priorIndex current r)
      (j := X.priorIndex current q) (by
        simpa [priorIndex] using hrq)
  firstInitial_eq_original := by
    have hindex :
        X.priorIndex current ⟨0, hcurrent⟩ = X.firstIndex := by
      apply Fin.ext
      rfl
    simpa [hindex] using X.originalHole_eq
  lastFinal_eq_current := by
    intro r hr
    exact X.chain
      (i := X.priorIndex current r)
      (j := current) (by
        simpa [priorIndex] using hr)
  priorPath_ne_current := by
    intro r
    apply X.path_pairwise
    intro hEq
    have hval := congrArg Fin.val hEq
    simp [priorIndex] at hval
    exact (Nat.ne_of_lt r.isLt) hval
  priorPath_pairwise := by
    intro r q hrq
    apply X.path_pairwise
    intro hEq
    apply hrq
    apply Fin.ext
    have hval := congrArg Fin.val hEq
    simpa [priorIndex] using hval
  earlierFirstIntroduced_uniquePath := by
    intro r
    exact X.firstIntroduced_uniquePath (X.priorIndex current r)
  currentRemoved_mem_original := by
    intro s
    exact X.removed_mem_original current s

/-- Every output path is represented by a literal finite block, and every
noninitial output block has a canonically constructed bounded history. -/
theorem output_path_has_finite_history
    (X : FiniteMixedSideSearchTrace S originalHole)
    {P : Set V} (hP : P ∈ S.paths) :
    ∃ i : Fin X.blockCount,
      Set.range (X.block i).path.vertex = P ∧
        (i.val = 0 ∨
          ∃ H : FiniteMixedSideLemma11AHistoryData
              (X.block i) originalHole,
            H.priorCount = i.val) := by
  obtain ⟨i, hiP⟩ := (X.output_path_iff P).mp hP
  refine ⟨i, hiP, ?_⟩
  by_cases hi : i.val = 0
  · exact Or.inl hi
  · right
    let H := X.finiteHistoryAt i (Nat.pos_of_ne_zero hi)
    exact ⟨H, rfl⟩

end FiniteMixedSideSearchTrace

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
