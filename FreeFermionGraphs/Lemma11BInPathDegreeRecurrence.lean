import FreeFermionGraphs.Lemma11BHoleVertexDegree

/-!
# Lemma 11(b): in-path degree recurrence

An in-path dependent vertex at step `s` is the vertex removed at step
`s - 1`. While it is still on that preceding hole its degree is two.
Removing it introduces an adjacent clone in place of its nonadjacent self,
raising the degree to three. Definition 20 raises it once more at step
`s`, giving degree four.

At every strictly later step, Definition 19's path indices show that the
vertex is adjacent to neither the introduced nor the removed path vertex,
so subsequent replacements preserve its degree.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The after-hole at the dependent vertex's current step has degree four
in the in-path branch. -/
theorem dependent_mem_path_current_degreeAfter_eq_four
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex) :
    (D.deformation.step
      ⟨s, D.index_lt_of_mem_dependentAt hu⟩).degreeAfter u = 4 := by
  obtain ⟨t, ht, hsucc, huRemoved⟩ :=
    D.dependent_mem_path_eq_previous_removed L hu huPath
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hij : previous.val + 1 = current.val := by
    simpa [previous, current, Nat.succ_eq_add_one] using hsucc
  have hbeforeTwo :
      (D.deformation.step previous).before.externalDegree u = 2 := by
    rw [huRemoved]
    exact
      (D.deformation.step previous).before.externalDegree_vertex_eq_two
        (D.deformation.step previous).removedIndex
  have huPreviousIntroduced :
      G.Adj u (D.deformation.step previous).introduced := by
    rw [huRemoved]
    exact
      (D.deformation.step previous).deformation.adj_clone.symm
  have huPreviousRemoved :
      ¬G.Adj u
        ((D.deformation.step previous).before.vertex
          (D.deformation.step previous).removedIndex) := by
    rw [huRemoved]
    exact G.loopless.irrefl u
  have hpreviousAfter :
      (D.deformation.step previous).degreeAfter u = 3 := by
    calc
      (D.deformation.step previous).degreeAfter u =
          (D.deformation.step previous).before.externalDegree u + 1 := by
        simpa [ConcreteDeformationStep.degreeAfter,
          ConcreteDeformationStep.after] using
          (D.deformation.step previous).deformation
            .externalDegree_deform_eq_add_one
              huPreviousIntroduced huPreviousRemoved
      _ = 2 + 1 := by rw [hbeforeTwo]
      _ = 3 := by omega
  have hcurrentBefore :
      (D.deformation.step current).degreeBefore u = 3 := by
    rw [← D.deformation.degreeAfter_eq_nextDegreeBefore
      (i := previous) (j := current) hij u]
    exact hpreviousAfter
  have huCurrent :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hcurrentAfter :
      (D.deformation.step current).degreeAfter u = 4 := by
    calc
      (D.deformation.step current).degreeAfter u =
          (D.deformation.step current).degreeBefore u + 1 :=
        (D.deformation.step current)
          .degreeAfter_eq_add_one_of_mem_dependentSet huCurrent
      _ = 3 + 1 := by rw [hcurrentBefore]
      _ = 4 := by omega
  simpa [current] using hcurrentAfter

/-- An in-path dependent vertex is nonadjacent to every vertex introduced
at a strictly later step. -/
theorem dependent_mem_path_not_adj_later_introduced
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (j : Fin D.deformation.stepCount)
    (hsj : s < j.val) :
    ¬G.Adj u (D.deformation.step j).introduced := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hui : u ∈ D.dependentAt i.val := by
    simpa [i] using hu
  obtain ⟨q, hqu, hqval⟩ :=
    D.dependent_mem_path_global_index L i hui huPath
  have hqval' : q.val + 1 = 2 * s := by
    simpa [i] using hqval
  intro huj
  have hadj :
      G.Adj
        (D.path.vertex q)
        (D.path.vertex (L.introducedPathIndex j)) := by
    rw [hqu, L.introduced_eq j]
    exact huj
  rcases (D.path.adj_iff q (L.introducedPathIndex j)).1 hadj with
    hforward | hbackward
  · have hjval := L.introduced_index_val j
    omega
  · have hjval := L.introduced_index_val j
    omega

/-- An in-path dependent vertex is nonadjacent to every vertex removed at a
strictly later step. -/
theorem dependent_mem_path_not_adj_later_removed
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (j : Fin D.deformation.stepCount)
    (hsj : s < j.val) :
    ¬G.Adj u
      ((D.deformation.step j).before.vertex
        (D.deformation.step j).removedIndex) := by
  let i : Fin D.deformation.stepCount :=
    ⟨s, D.index_lt_of_mem_dependentAt hu⟩
  have hui : u ∈ D.dependentAt i.val := by
    simpa [i] using hu
  obtain ⟨q, hqu, hqval⟩ :=
    D.dependent_mem_path_global_index L i hui huPath
  have hqval' : q.val + 1 = 2 * s := by
    simpa [i] using hqval
  intro huj
  have hadj :
      G.Adj
        (D.path.vertex q)
        (D.path.vertex (L.removedPathIndex j)) := by
    rw [hqu, L.removed_eq j]
    exact huj
  rcases (D.path.adj_iff q (L.removedPathIndex j)).1 hadj with
    hforward | hbackward
  · have hjval := L.removed_index_val j
    omega
  · have hjval := L.removed_index_val j
    omega

/-- Every step strictly after the dependent step preserves the in-path
vertex's external degree. -/
theorem dependent_mem_path_later_degreeAfter_eq_degreeBefore
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huPath : u ∈ Set.range D.path.vertex)
    (j : Fin D.deformation.stepCount)
    (hsj : s < j.val) :
    (D.deformation.step j).degreeAfter u =
      (D.deformation.step j).degreeBefore u := by
  have huIntroduced :
      ¬G.Adj u (D.deformation.step j).introduced :=
    D.dependent_mem_path_not_adj_later_introduced
      L hu huPath j hsj
  have huRemoved :
      ¬G.Adj u
        ((D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex) :=
    D.dependent_mem_path_not_adj_later_removed
      L hu huPath j hsj
  simpa [ConcreteDeformationStep.degreeAfter,
    ConcreteDeformationStep.degreeBefore,
    ConcreteDeformationStep.after] using
    (D.deformation.step j).deformation.externalDegree_deform_eq
      (iff_of_false huIntroduced huRemoved)

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
