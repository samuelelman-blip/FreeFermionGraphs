import FreeFermionGraphs.Lemma11BCommonForcesPreviousIntroduced

/-!
# Lemma 11(b): the half-length two obstruction

When the alternating hole has half-length two, its cyclic order is

`b r - a r - b (next r) - a (next r) - b r`.

If an outside dependent vertex misses both the common vertex
`b (next r)` and the preceding introduced clone, claw-freeness first
forces adjacency to `b r`.  That other `b`-vertex then centers the claw
displayed in the paper.  Hence the dependent vertex must neighbor the
preceding introduced vertex.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- A fixed-point-free `next` map on two indices is an involution. -/
theorem next_next_eq_of_two
    (C : EvenHoleLabeling G 2) (r : Fin 2) :
    C.next (C.next r) = r := by
  apply Fin.ext
  have hr : r.val < 2 := r.isLt
  have hn : (C.next r).val < 2 := (C.next r).isLt
  have hnn :
      (C.next (C.next r)).val < 2 :=
    (C.next (C.next r)).isLt
  have hrn : r.val ≠ (C.next r).val := by
    intro hval
    exact C.next_ne r (Fin.ext hval.symm)
  have hnnn :
      (C.next (C.next r)).val ≠ (C.next r).val := by
    intro hval
    exact C.next_ne (C.next r) (Fin.ext hval)
  omega

/-- The two claw arguments for a four-vertex alternating hole. -/
theorem adj_clone_of_halfLength_two
    (C : EvenHoleLabeling G 2)
    (hclaw : G.IsClawFree)
    {introduced u : V} {r : Fin 2}
    (hc : C.CloneAt introduced r)
    (huOriginal : G.Adj u (C.a r))
    (huNotCommon : ¬G.Adj u (C.b (C.next r)))
    (huNotCurrent : ¬G.Adj u (C.a (C.next r)))
    (huNeB : u ≠ C.b r)
    (huNeCommon : u ≠ C.b (C.next r))
    (huNeIntroduced : u ≠ introduced)
    (huNeCurrent : u ≠ C.a (C.next r)) :
    G.Adj u introduced := by
  have hbNe : C.b r ≠ C.b (C.next r) :=
    (C.b_ne_next r)
  have huB : G.Adj u (C.b r) := by
    rcases hclaw
        huOriginal.symm
        (C.adj_a_b r)
        (C.adj_a_b_next r)
        huNeB huNeCommon hbNe with
      huB | huCommon | hbb
    · exact huB
    · exact (huNotCommon huCommon).elim
    · exact (C.adj_bb r (C.next r) hbb).elim
  have hcurrentB :
      G.Adj (C.a (C.next r)) (C.b r) := by
    have h :=
      C.adj_a_b_next (C.next r)
    rw [C.next_next_eq_of_two r] at h
    exact h
  have hIntroducedCurrentNe :
      introduced ≠ C.a (C.next r) := by
    intro hEq
    apply hc.outside
    rw [hEq]
    exact C.a_mem_carrier (C.next r)
  rcases hclaw
      huB.symm
      hc.adj_b.symm
      hcurrentB.symm
      huNeIntroduced huNeCurrent hIntroducedCurrentNe with
    huIntroduced | huCurrent | hIntroducedCurrent
  · exact huIntroduced
  · exact (huNotCurrent huCurrent).elim
  · exact (hc.not_adj_a_next hIntroducedCurrent).elim

end EvenHoleLabeling

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- In the half-length two outside branch, every commuting dependent vertex
neighbors the preceding introduced vertex.  This eliminates the paper's
exceptional `k = 2` case. -/
theorem adj_previous_introduced_of_halfLength_two
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence 2)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    ∃ previous : Fin D.deformation.stepCount,
      previous.val + 1 = s ∧
      G.Adj u (D.deformation.step previous).introduced := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  obtain ⟨t, ht, hts, huPreviousRemoved⟩ :=
    D.adj_previous_removed_of_outside_commuting
      M L hclaw horder hopposite hu huOutside hnotAnti
  let previous : Fin D.deformation.stepCount := ⟨t, ht⟩
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  have hij : previous.val + 1 = current.val := by
    dsimp [previous, current]
    omega
  let C : EvenHoleLabeling G 2 := A.labeling previous
  let r : Fin 2 := A.removedAIndex previous
  let hc : C.CloneAt
      (D.deformation.step previous).introduced r := by
    simpa [C, r] using A.cloneAt previous
  have hCurrentRemoved :
      (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex =
        C.a (C.next r) := by
    simpa [C, r, current] using
      A.toAlternatingHoleCoordinates.next_removed_eq hij
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  have huNotCurrent :
      ¬G.Adj u (C.a (C.next r)) := by
    intro huCurrent
    apply hmem.2.2.2
    rw [hCurrentRemoved]
    exact huCurrent
  have houtsideCurrent :=
    M.outsideHole current huStep
  have hbCurrent :
      C.b r ∈
        Set.range (D.deformation.step current).before.vertex := by
    rw [← A.carrier_eq current]
    rw [A.transport_eq hij]
    simpa [C, r, hc] using
      ((C.deform hc).b_mem_carrier r)
  have hbNextCurrent :
      C.b (C.next r) ∈
        Set.range (D.deformation.step current).before.vertex := by
    rw [← A.carrier_eq current]
    rw [A.transport_eq hij]
    simpa [C, r, hc] using
      ((C.deform hc).b_mem_carrier (C.next r))
  have huNeB : u ≠ C.b r := by
    intro huB
    apply houtsideCurrent
    exact Set.mem_insert_iff.2
      (Or.inr (huB.symm ▸ hbCurrent))
  have huNeCommon : u ≠ C.b (C.next r) := by
    intro huB
    apply houtsideCurrent
    exact Set.mem_insert_iff.2
      (Or.inr (huB.symm ▸ hbNextCurrent))
  have huNeIntroduced :
      u ≠ (D.deformation.step previous).introduced := by
    intro huIntroduced
    apply huOutside
    refine
      ⟨L.introducedPathIndex previous, ?_⟩
    exact
      (L.introduced_eq previous).trans
        huIntroduced.symm
  have huNeCurrent : u ≠ C.a (C.next r) := by
    intro huCurrent
    apply houtsideCurrent
    apply Set.mem_insert_iff.2
    right
    rw [← hCurrentRemoved, huCurrent]
    exact
      ⟨(D.deformation.step current).removedIndex, rfl⟩
  by_cases huCommon :
      G.Adj u (C.b (C.next r))
  · refine ⟨previous, by simpa [previous] using hij, ?_⟩
    exact D.adj_previous_introduced_of_adj_common
      L hclaw hs previous
      (by simpa [current] using hij)
      huOutside
      (by simpa [C, r, hc] using hc.adj_b_next)
      (by
        rw [hCurrentRemoved]
        exact C.adj_a_b (C.next r))
      huCommon
      (by
        simpa [current] using hmem.2.2.2)
  · have huOriginal : G.Adj u (C.a r) := by
      rw [← A.removed_eq previous]
      exact huPreviousRemoved
    have huIntroduced :
        G.Adj u (D.deformation.step previous).introduced := by
      exact C.adj_clone_of_halfLength_two
        hclaw hc huOriginal huCommon huNotCurrent
        huNeB huNeCommon huNeIntroduced huNeCurrent
    exact ⟨previous, by simpa [previous] using hij, huIntroduced⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
