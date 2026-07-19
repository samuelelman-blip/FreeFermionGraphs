import FreeFermionGraphs.Lemma11BRemovedVertex

/-!
# Lemma 11(b): the in-path vertex was removed previously

All steps in a concrete path deformation share one active path. Expressing
Definition 19's indices directly in that common path lets us compare labels
at consecutive steps.

An in-path dependent vertex at step `s` has path index `2s - 1`, while
the removed vertex at step `s - 1` has the same index. Injectivity of the
path labeling therefore identifies the two vertices. The carrier-chain
lemma then proves that this dependent vertex is outside the current
before-hole.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Definition 19's overlap-aware labeling, normalized to the common active
path of the whole deformation block. -/
structure Definition19GlobalOverlapPathOrder
    (D : ConcretePathDeformation O Cprime) where
  introducedPathIndex :
    ∀ i : Fin D.deformation.stepCount, Fin D.path.card
  removedPathIndex :
    ∀ i : Fin D.deformation.stepCount, Fin D.path.card
  introduced_eq :
    ∀ i : Fin D.deformation.stepCount,
      D.path.vertex (introducedPathIndex i) =
        (D.deformation.step i).introduced
  removed_eq :
    ∀ i : Fin D.deformation.stepCount,
      D.path.vertex (removedPathIndex i) =
        (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex
  introduced_index_val :
    ∀ i : Fin D.deformation.stepCount,
      (introducedPathIndex i).val = 2 * i.val
  removed_index_val :
    ∀ i : Fin D.deformation.stepCount,
      (removedPathIndex i).val = 2 * i.val + 1
  prime_neighbor_precedes_introduced :
    ∀ (i : Fin D.deformation.stepCount) (q : Fin D.path.card),
      q ≠ removedPathIndex i →
      G.Adj
        (D.path.vertex (introducedPathIndex i))
        (D.path.vertex q) →
      D.path.vertex q ∈ Cprime →
      q.val + 1 = (introducedPathIndex i).val

/-- Common-path form of the in-path index theorem. -/
theorem dependent_mem_path_global_index
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (i : Fin D.deformation.stepCount)
    {u : V}
    (hu : u ∈ D.dependentAt i.val)
    (huPath : u ∈ Set.range D.path.vertex) :
    ∃ q : Fin D.path.card,
      D.path.vertex q = u ∧
      q.val + 1 = 2 * i.val := by
  have huStep :
      u ∈ (D.deformation.step i).dependentSet := by
    simpa [dependentAt, i.isLt] using hu
  obtain ⟨q, hqu⟩ := huPath
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step i)).1 huStep
  have hqRemoved : q ≠ L.removedPathIndex i := by
    intro hq
    subst q
    apply hmem.2.2.1
    calc
      u = D.path.vertex (L.removedPathIndex i) := hqu.symm
      _ = (D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex :=
        L.removed_eq i
  have hadj :
      G.Adj
        (D.path.vertex (L.introducedPathIndex i))
        (D.path.vertex q) := by
    rw [L.introduced_eq i, hqu]
    exact hmem.2.1.symm
  have hqPrime : D.path.vertex q ∈ Cprime := by
    rw [hqu]
    exact hmem.1
  exact ⟨q, hqu,
    (L.prime_neighbor_precedes_introduced
      i q hqRemoved hadj hqPrime).trans
        (L.introduced_index_val i)⟩

/-- The in-path dependent vertex at step `s` is exactly the vertex removed
at the preceding step. -/
theorem dependent_mem_path_eq_previous_removed
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    ∃ t : Nat, ∃ ht : t < D.deformation.stepCount,
      Nat.succ t = s ∧
      u =
        (D.deformation.step ⟨t, ht⟩).before.vertex
          (D.deformation.step ⟨t, ht⟩).removedIndex := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  have huCurrent : u ∈ D.dependentAt current.val := by
    simpa [current] using hu
  obtain ⟨q, hqu, hqval⟩ :=
    D.dependent_mem_path_global_index L current huCurrent huPath
  have hqval' : q.val + 1 = 2 * s := by
    simpa [current] using hqval
  have hsPos : 0 < s := by
    omega
  let t : Nat := s - 1
  have ht : t < D.deformation.stepCount := by
    dsimp [t]
    omega
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  have hsucc : Nat.succ t = s := by
    dsimp [t]
    omega
  have hremovedVal :
      (L.removedPathIndex previous).val =
        2 * (s - 1) + 1 := by
    simpa [previous, t] using L.removed_index_val previous
  have hqRemoved :
      q = L.removedPathIndex previous := by
    apply Fin.ext
    omega
  refine ⟨t, ht, hsucc, ?_⟩
  calc
    u = D.path.vertex q := hqu.symm
    _ = D.path.vertex (L.removedPathIndex previous) := by
      rw [hqRemoved]
    _ = (D.deformation.step previous).before.vertex
        (D.deformation.step previous).removedIndex :=
      L.removed_eq previous

/-- Therefore an in-path dependent vertex is absent from the current
before-hole: it was removed by the immediately preceding step. -/
theorem dependent_mem_path_not_mem_current_before
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    u ∉
      Set.range
        (D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).before.vertex := by
  obtain ⟨t, ht, hsucc, huRemoved⟩ :=
    D.dependent_mem_path_eq_previous_removed L hu huPath
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hij : previous.val + 1 = current.val := by
    simpa [previous, current, Nat.succ_eq_add_one] using hsucc
  have hnot :=
    D.deformation.previous_removed_not_mem_before
      (i := previous) (j := current) hij
  intro huBefore
  apply hnot
  rw [← huRemoved]
  simpa [current] using huBefore

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
