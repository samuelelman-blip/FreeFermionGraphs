import FreeFermionGraphs.Lemma11BOutsideCommonNeighborConfig

/-!
# Lemma 11(b): adjacency to the common vertex forces the previous introduction

In the paper's outside-path branch, suppose `u` neighbors the common
vertex `w_(s-1)`.  If `u` missed the preceding introduced vertex, then
`w_(s-1)` would be the center of a claw with leaves `u`,
`j_(s-2)`, and `k_(s-1)`.

Definition 19's path order proves that the latter two leaves are
nonadjacent, while Definition 20 says that `u` misses `k_(s-1)`.
Therefore claw-freeness forces the edge `u-j_(s-2)`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- Adjacency to the consecutive-step common vertex forces adjacency to the
preceding introduced path vertex. -/
theorem adj_previous_introduced_of_adj_common
    (D : ConcretePathDeformation O Cprime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    {s : Nat} {u w : V}
    (hs : s < D.deformation.stepCount)
    (previous : Fin D.deformation.stepCount)
    (hprevious : previous.val + 1 = s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hwPreviousIntroduced :
      G.Adj (D.deformation.step previous).introduced w)
    (hwCurrentRemoved :
      G.Adj
        ((D.deformation.step ⟨s, hs⟩).before.vertex
          (D.deformation.step ⟨s, hs⟩).removedIndex)
        w)
    (huCommon : G.Adj u w)
    (huNotCurrentRemoved :
      ¬G.Adj u
        ((D.deformation.step ⟨s, hs⟩).before.vertex
          (D.deformation.step ⟨s, hs⟩).removedIndex)) :
    G.Adj u (D.deformation.step previous).introduced := by
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  let p : Fin D.path.card := L.introducedPathIndex previous
  let q : Fin D.path.card := L.removedPathIndex current
  have hpval : p.val = 2 * previous.val := by
    simpa [p] using L.introduced_index_val previous
  have hqval : q.val = 2 * s + 1 := by
    simpa [q, current] using L.removed_index_val current
  have hpq : p ≠ q := by
    intro hpq
    have hval := congrArg Fin.val hpq
    omega
  have hpqVertex : D.path.vertex p ≠ D.path.vertex q := by
    intro hpq'
    exact hpq (D.path.injective hpq')
  have hpqNotAdj :
      ¬G.Adj (D.path.vertex p) (D.path.vertex q) := by
    intro hadj
    rcases (D.path.adj_iff p q).1 hadj with
      hpq' | hqp' <;> omega
  have hPreviousCurrentNotAdj :
      ¬G.Adj
        (D.deformation.step previous).introduced
        ((D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex) := by
    rw [← L.introduced_eq previous, ← L.removed_eq current]
    exact hpqNotAdj
  have huPreviousNe :
      u ≠ (D.deformation.step previous).introduced := by
    intro hup
    apply huOutside
    refine ⟨p, ?_⟩
    exact (L.introduced_eq previous).trans hup.symm
  have huCurrentNe :
      u ≠
        (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex := by
    intro huq
    apply huOutside
    refine ⟨q, ?_⟩
    exact (L.removed_eq current).trans huq.symm
  have hPreviousCurrentNe :
      (D.deformation.step previous).introduced ≠
        (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex := by
    intro hpq'
    apply hpqVertex
    exact
      (L.introduced_eq previous).trans
        (hpq'.trans (L.removed_eq current).symm)
  rcases hclaw
      huCommon.symm
      hwPreviousIntroduced.symm
      hwCurrentRemoved.symm
      huPreviousNe huCurrentNe hPreviousCurrentNe with
    huPrevious | huCurrent | hPreviousCurrent
  · exact huPrevious
  · exact (huNotCurrentRemoved (by
      simpa [current] using huCurrent)).elim
  · exact (hPreviousCurrentNotAdj (by
      simpa [current] using hPreviousCurrent)).elim

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
