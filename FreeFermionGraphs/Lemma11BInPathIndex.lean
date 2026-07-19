import FreeFermionGraphs.Lemma11BInPathDependent

/-!
# Lemma 11(b): the index of an in-path dependent vertex

Under Definition 19's order, the introduced vertex at deformation index
`s` has path index `2s`. The overlap-aware local theorem therefore
identifies any dependent path vertex with index `2s - 1`.

In particular, such a vertex cannot occur at step zero, and every in-path
case has a genuine preceding deformation step. These are the first index
reductions in the paper's in-path branch.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- At a Fin-indexed step `i`, an in-path dependent vertex has path index
immediately before `2 * i`. -/
theorem dependent_mem_path_index
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19OverlapPathOrder D)
    (i : Fin D.deformation.stepCount)
    {u : V}
    (hu : u ∈ D.dependentAt i.val)
    (huPath : u ∈ Set.range D.path.vertex) :
    ∃ q : Fin (D.deformation.step i).activePath.card,
      (D.deformation.step i).activePath.vertex q = u ∧
      q.val + 1 = 2 * i.val := by
  have huStep :
      u ∈ (D.deformation.step i).dependentSet := by
    simpa [dependentAt, i.isLt] using hu
  have huActive :
      u ∈ Set.range (D.deformation.step i).activePath.vertex := by
    rw [D.activePath_eq i]
    exact huPath
  obtain ⟨q, hqu, hq⟩ :=
    (D.deformation.step i).dependent_path_vertex_precedes_introduced
      (L.stepLabeling i) huStep huActive
  exact ⟨q, hqu, hq.trans (L.introduced_index_val i)⟩

/-- A dependent vertex lying on the active path can only occur at a
positive deformation index. -/
theorem dependent_mem_path_step_pos
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19OverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    0 < s := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hui : u ∈ D.dependentAt i.val := by
    simpa [i] using hu
  obtain ⟨q, _hqu, hq⟩ :=
    D.dependent_mem_path_index L i hui huPath
  simp only [i] at hq
  omega

/-- Hence the paper's in-path branch always has a preceding deformation
step. -/
theorem dependent_mem_path_has_previous_step
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19OverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    ∃ t : Nat, Nat.succ t = s := by
  have hs : 0 < s :=
    D.dependent_mem_path_step_pos L hu huPath
  exact ⟨s - 1, by omega⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
