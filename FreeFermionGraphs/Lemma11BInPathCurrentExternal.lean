import FreeFermionGraphs.Lemma11BInPathPreviousRemoval

/-!
# Lemma 11(b): current-hole externality in the in-path branch

A vertex absent from an indexed hole remains absent after a single-vertex
deformation unless it is the introduced vertex itself. A dependent vertex
is adjacent to the introduced vertex, so graph looplessness makes them
distinct.

Combining this with the previous-removal theorem proves that an in-path
dependent vertex is external to both the before-hole and after-hole at its
current deformation step.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- A vertex outside the old hole and distinct from the introduced vertex
is outside the deformed hole. -/
theorem not_mem_deform_of_not_mem_of_ne
    (C : IndexedInducedHole G)
    {introduced u : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i)
    (huBefore : u ∉ Set.range C.vertex)
    (huIntroduced : u ≠ introduced) :
    u ∉ Set.range (C.deform h).vertex := by
  rintro ⟨q, hq⟩
  by_cases hqi : q = i
  · subst q
    have hintroduced : introduced = u := by
      simpa using hq
    exact huIntroduced hintroduced.symm
  · apply huBefore
    refine ⟨q, ?_⟩
    have haway :
        (C.deform h).vertex q = C.vertex q :=
      C.deform_vertex_away h hqi
    calc
      C.vertex q = (C.deform h).vertex q := haway.symm
      _ = u := hq

end IndexedInducedHole

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcreteDeformationStep

/-- Step-level externality transport. -/
theorem not_mem_after_of_not_mem_before_of_ne
    (S : ConcreteDeformationStep O Cprime)
    {u : V}
    (huBefore : u ∉ Set.range S.before.vertex)
    (huIntroduced : u ≠ S.introduced) :
    u ∉ Set.range S.after.vertex := by
  simpa [after] using
    S.before.not_mem_deform_of_not_mem_of_ne
      S.deformation huBefore huIntroduced

end ConcreteDeformationStep

namespace ConcretePathDeformation

/-- An in-path dependent vertex is external to the after-hole of its current
deformation step. -/
theorem dependent_mem_path_not_mem_current_after
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    u ∉
      Set.range
        (D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).after.vertex := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have huStep :
      u ∈ (D.deformation.step i).dependentSet := by
    simpa [i] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step i)).1 huStep
  have huBefore :
      u ∉ Set.range (D.deformation.step i).before.vertex := by
    simpa [i] using
      D.dependent_mem_path_not_mem_current_before L hu huPath
  have huIntroduced :
      u ≠ (D.deformation.step i).introduced :=
    hmem.2.1.ne
  simpa [i] using
    (D.deformation.step i).not_mem_after_of_not_mem_before_of_ne
      huBefore huIntroduced

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
