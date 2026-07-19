import FreeFermionGraphs.Lemma11BInPathIndex

/-!
# Removed vertices in a concrete deformation

Replacing one indexed-hole vertex by a vertex outside the hole removes the
old vertex from the new carrier. Consecutive concrete deformation steps
identify the new carrier with the next before-carrier, so the removed vertex
is also absent immediately before the next step.

For the in-path branch of Lemma 11(b), this is the structural reason that
the overlap vertex `k_(s-2)` is external after its preceding deformation.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace IndexedInducedHole

/-- The replaced vertex does not occur in the deformed indexed hole. -/
theorem removed_vertex_not_mem_deform
    (C : IndexedInducedHole G)
    {introduced : V} {i : Fin C.card}
    (h : C.SingleVertexDeformation introduced i) :
    C.vertex i ∉ Set.range (C.deform h).vertex := by
  rintro ⟨q, hq⟩
  by_cases hqi : q = i
  · subst q
    have hintroduced :
        introduced = C.vertex i := by
      simpa using hq
    exact h.outside ⟨i, hintroduced.symm⟩
  · have haway :
        (C.deform h).vertex q = C.vertex q :=
      C.deform_vertex_away h hqi
    have hvertices :
        C.vertex q = C.vertex i := by
      calc
        C.vertex q = (C.deform h).vertex q := haway.symm
        _ = C.vertex i := hq
    exact hqi (C.injective hvertices)

end IndexedInducedHole

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcreteDeformationStep

/-- Step-level form: the removed vertex is absent from the after-hole. -/
theorem removed_not_mem_after
    (S : ConcreteDeformationStep O Cprime) :
    S.before.vertex S.removedIndex ∉
      Set.range S.after.vertex := by
  simpa [after] using
    S.before.removed_vertex_not_mem_deform S.deformation

end ConcreteDeformationStep

namespace ConcreteDeformation

/-- The vertex removed at one step is absent from the before-hole of the
immediately following step. -/
theorem previous_removed_not_mem_before
    (D : ConcreteDeformation O Cprime)
    {i j : Fin D.stepCount}
    (hij : i.val + 1 = j.val) :
    (D.step i).before.vertex (D.step i).removedIndex ∉
      Set.range (D.step j).before.vertex := by
  intro hmem
  have hchain :
      Set.range (D.step i).after.vertex =
        Set.range (D.step j).before.vertex :=
    D.carrier_chain hij
  have hmemAfter :
      (D.step i).before.vertex (D.step i).removedIndex ∈
        Set.range (D.step i).after.vertex := by
    rw [hchain]
    exact hmem
  exact (D.step i).removed_not_mem_after hmemAfter

end ConcreteDeformation

end FixedPairingPathFamily

end SimpleGraph
