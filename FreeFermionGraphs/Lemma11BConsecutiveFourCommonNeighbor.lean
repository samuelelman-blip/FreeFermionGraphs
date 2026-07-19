import FreeFermionGraphs.Lemma11BOutsideFourPathBlock

/-!
# Lemma 11(b): the common neighbor of two consecutive deformation pairs

The paper names a vertex w_(s-1) adjacent to the introduced and removed
vertices at each of two consecutive deformation steps. The essential input
is that the two original removed vertices share a neighbor on the earlier
hole.

This module proves the deformation-theoretic bridge. A shared original
neighbor is not removed at the first step, so the carrier chain places it on
the next before-hole. The clone property then makes it adjacent to both
introduced vertices. The alternating hole coloring puts the shared neighbor
in C_b.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}

namespace ConcretePathDeformation

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

/-- The remaining alternating-hole input for consecutive steps: their two
removed vertices share a neighbor on the earlier before-hole. -/
def ConsecutiveRemovedCommonNeighborRule
    (D : ConcretePathDeformation O Cprime) : Prop :=
  ∀ ⦃i j : Fin D.deformation.stepCount⦄,
    i.val + 1 = j.val →
    ∃ w : V,
      w ∈ Set.range (D.deformation.step i).before.vertex ∧
      G.Adj
        ((D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex) w ∧
      G.Adj
        ((D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex) w

/-- The complete four-vertex common-neighbor certificate used as
w_(s-1) in the paper. -/
def HasConsecutiveFourCommonNeighbor
    (D : ConcretePathDeformation O Cprime)
    (i j : Fin D.deformation.stepCount) : Prop :=
  ∃ w : V,
    w ∈ Set.range (D.deformation.step i).before.vertex ∧
    w ∈ Set.range (D.deformation.step j).before.vertex ∧
    G.Adj (D.deformation.step i).introduced w ∧
    G.Adj
      ((D.deformation.step i).before.vertex
        (D.deformation.step i).removedIndex) w ∧
    G.Adj (D.deformation.step j).introduced w ∧
    G.Adj
      ((D.deformation.step j).before.vertex
        (D.deformation.step j).removedIndex) w ∧
    w ∈ O.Cb

/-- A common neighbor of the two consecutive removed vertices persists
through the first deformation, becomes adjacent to both clones, and lies in
the original-side class C_b. -/
theorem hasConsecutiveFourCommonNeighbor_of_removedCommonNeighbor
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    {i j : Fin D.deformation.stepCount}
    (hij : i.val + 1 = j.val)
    {w : V}
    (hwBefore :
      w ∈ Set.range (D.deformation.step i).before.vertex)
    (hiw :
      G.Adj
        ((D.deformation.step i).before.vertex
          (D.deformation.step i).removedIndex) w)
    (hjw :
      G.Adj
        ((D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex) w) :
    D.HasConsecutiveFourCommonNeighbor i j := by
  have hwBeforeCopy := hwBefore
  obtain ⟨r, hrw⟩ := hwBefore
  have hri :
      r ≠ (D.deformation.step i).removedIndex := by
    intro hri
    subst r
    rw [hrw] at hiw
    exact G.loopless.irrefl w hiw
  have hiIntroduced :
      G.Adj (D.deformation.step i).introduced w := by
    have hclone :=
      (D.deformation.step i).deformation.adj_of_clone_adj
        (show
          G.Adj
            ((D.deformation.step i).before.vertex
              (D.deformation.step i).removedIndex)
            ((D.deformation.step i).before.vertex r) by
          simpa [hrw] using hiw)
    simpa [hrw] using hclone
  have hwAfter :
      w ∈ Set.range (D.deformation.step i).after.vertex := by
    refine ⟨r, ?_⟩
    calc
      (D.deformation.step i).after.vertex r =
          (D.deformation.step i).before.vertex r := by
        simpa [ConcreteDeformationStep.after] using
          (D.deformation.step i).before.deform_vertex_away
            (D.deformation.step i).deformation hri
      _ = w := hrw
  have hwNextBefore :
      w ∈ Set.range (D.deformation.step j).before.vertex := by
    rw [← D.deformation.carrier_chain hij]
    exact hwAfter
  have hwNextBeforeCopy := hwNextBefore
  obtain ⟨q, hqw⟩ := hwNextBefore
  have hjIntroduced :
      G.Adj (D.deformation.step j).introduced w := by
    have hremoved :
        G.Adj
          ((D.deformation.step j).before.vertex
            (D.deformation.step j).removedIndex)
          ((D.deformation.step j).before.vertex q) := by
      simpa [hqw] using hjw
    have hclone :=
      (D.deformation.step j).deformation.adj_of_clone_adj
        hremoved
    simpa [hqw] using hclone
  have hwCb : w ∈ O.Cb := by
    rcases (M.stepGeometry i).before_subset hwBeforeCopy with
      hwCa | hwCb
    · exact ((M.stepGeometry i).ca_independent
        (M.stepGeometry i).removed_ca hwCa hiw).elim
    · exact hwCb
  exact ⟨w, hwBeforeCopy, hwNextBeforeCopy,
    hiIntroduced, hiw, hjIntroduced, hjw, hwCb⟩

/-- The family rule supplies the paper's complete w_(s-1) certificate at
every pair of consecutive deformation steps. -/
theorem consecutiveFourCommonNeighborRule_of_removedCommonNeighbors
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (hcommon : D.ConsecutiveRemovedCommonNeighborRule) :
    ∀ ⦃i j : Fin D.deformation.stepCount⦄,
      i.val + 1 = j.val →
      D.HasConsecutiveFourCommonNeighbor i j := by
  intro i j hij
  obtain ⟨w, hw, hiw, hjw⟩ := hcommon hij
  exact
    D.hasConsecutiveFourCommonNeighbor_of_removedCommonNeighbor
      M hij hw hiw hjw

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
