import FreeFermionGraphs.Lemma11BHalfLengthGtThree
import FreeFermionGraphs.Lemma11BConcreteDegree

/-!
# Lemma 11(b): the half-length-three exceptional branch

For a six-vertex alternating hole, the long-hole claw obstruction no longer
forces adjacency to the preceding introduced clone.  Instead, when the
dependent vertex misses the common `b`-vertex, the two local claw arguments
exhibit four distinct neighbors on the preceding hole.  This is exactly the
exceptional degree-four configuration in the paper.

The concrete theorem below packages the resulting dichotomy: either the
vertex neighbors the preceding introduced path vertex, or the preceding
indexed hole carries an explicit four-neighbor certificate.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- In the exceptional six-cycle branch, missing the consecutive common
`b`-vertex forces three further neighbors on the preceding labeled hole.
Together with the preceding removed vertex these are the four neighbors
displayed in the paper. -/
theorem four_previous_neighbors_of_halfLength_three_of_not_common
    (C : EvenHoleLabeling G 3)
    (hclaw : G.IsClawFree)
    {previousIntroduced currentIntroduced u : V}
    {r : Fin 3}
    (hprevious : C.CloneAt previousIntroduced r)
    (hcurrent :
      (C.deform hprevious).CloneAt
        currentIntroduced ((C.deform hprevious).next r))
    (huOutside :
      u ∉ Set.insert currentIntroduced
        (C.deform hprevious).carrier)
    (huPreviousOriginal : G.Adj u (C.a r))
    (huCurrentIntroduced : G.Adj u currentIntroduced)
    (huNotCurrentOriginal :
      ¬G.Adj u
        ((C.deform hprevious).a
          ((C.deform hprevious).next r)))
    (huNotCommon :
      ¬G.Adj u
        ((C.deform hprevious).b
          ((C.deform hprevious).next r))) :
    u ∉ C.carrier ∧
      G.Adj u (C.b r) ∧
      G.Adj u (C.b (C.next (C.next r))) ∧
      G.Adj u (C.a (C.next (C.next r))) := by
  let C1 : EvenHoleLabeling G 3 := C.deform hprevious
  have huNe_of_mem :
      ∀ {x : V}, x ∈ C1.carrier → u ≠ x := by
    intro x hx hux
    apply huOutside
    exact Set.mem_insert_iff.2
      (Or.inr (hux.symm ▸ hx))
  have huNeB : u ≠ C.b r := by
    apply huNe_of_mem
    simpa [C1] using C1.b_mem_carrier r
  have huNeCommon : u ≠ C.b (C.next r) := by
    apply huNe_of_mem
    simpa [C1] using C1.b_mem_carrier (C1.next r)
  have hbNe : C.b r ≠ C.b (C.next r) :=
    (C.b_ne_next r).symm
  have huB : G.Adj u (C.b r) := by
    rcases hclaw
        huPreviousOriginal.symm
        (C.adj_a_b r)
        (C.adj_a_b_next r)
        huNeB huNeCommon hbNe with
      huB | huCommon | hbb
    · exact huB
    · exact (huNotCommon (by
        simpa [C1] using huCommon)).elim
    · exact (C.adj_bb r (C.next r) hbb).elim
  have hside :=
    hcurrent.dependent_forces_side
      hclaw huOutside
      (Or.inl
        ⟨huCurrentIntroduced,
          by simpa [C1] using huNotCurrentOriginal⟩)
  have hfar :
      G.Adj u (C1.b (C1.next (C1.next r))) ∧
        G.Adj u (C1.a (C1.next (C1.next r))) := by
    rcases hside with hleft | hright
    · exact (huNotCommon (by
        simpa [C1] using hleft.1)).elim
    · exact hright
  have huBNextNext :
      G.Adj u (C.b (C.next (C.next r))) := by
    simpa [C1] using hfar.1
  have hnextNextNe : C.next (C.next r) ≠ r :=
    C.next_next_ne (by omega) r
  have hfarA :
      C1.a (C1.next (C1.next r)) =
        C.a (C.next (C.next r)) := by
    change
      (C.deform hprevious).a
          ((C.deform hprevious).next
            ((C.deform hprevious).next r)) =
        C.a (C.next (C.next r))
    rw [C.deform_next, C.deform_next]
    exact C.deform_a_away hprevious hnextNextNe
  have huANextNext :
      G.Adj u (C.a (C.next (C.next r))) := by
    rw [← hfarA]
    exact hfar.2
  have huOutsideC : u ∉ C.carrier := by
    intro huC
    by_cases hua : u = C.a r
    · have huu : G.Adj u u := by
        simpa [hua] using huPreviousOriginal
      exact (G.loopless.irrefl u) huu
    · apply huOutside
      apply Set.mem_insert_iff.2
      right
      rw [C.deform_carrier hprevious]
      exact C.mem_deformedCarrier_of_mem huC hua
  exact
    ⟨huOutsideC, huB, huBNextNext, huANextNext⟩

end EvenHoleLabeling

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- At half-length three, the outside branch has precisely the paper's
exceptional dichotomy: the preceding introduced edge exists, or the
preceding hole has four explicit external neighbors. -/
theorem previous_introduced_or_four_previous_neighbors_of_halfLength_three
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence 3)
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
        (G.Adj u (D.deformation.step previous).introduced ∨
          (D.deformation.step previous).before.HasFourDistinctExternalNeighbors u) := by
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
  let C : EvenHoleLabeling G 3 := A.labeling previous
  let r : Fin 3 := A.removedAIndex previous
  let hprevious := A.cloneAt previous
  let C1 : EvenHoleLabeling G 3 := C.deform hprevious
  have hcurrent :
      C1.CloneAt
        (D.deformation.step current).introduced
        (C1.next r) := by
    have h := A.cloneAt current
    rw [A.transport_eq hij] at h
    rw [A.removed_index_next hij] at h
    simpa [C, C1, r, hprevious] using h
  have hcarrierCurrent :
      C1.carrier =
        Set.range (D.deformation.step current).before.vertex := by
    calc
      C1.carrier = (A.labeling current).carrier := by
        rw [A.transport_eq hij]
      _ = _ := A.carrier_eq current
  have hCurrentRemoved :
      (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex =
        C1.a (C1.next r) := by
    have h := A.removed_eq current
    rw [A.transport_eq hij] at h
    rw [A.removed_index_next hij] at h
    simpa [C, C1, r, hprevious] using h
  have huStep :
      u ∈ (D.deformation.step current).dependentSet := by
    simpa [current] using
      D.mem_step_dependentSet_of_mem_dependentAt hu
  have hmem :=
    (ConcreteDeformationStep.mem_dependentSet
      (D.deformation.step current)).1 huStep
  have huOutsideCurrent :
      u ∉ Set.insert (D.deformation.step current).introduced
        C1.carrier := by
    rw [hcarrierCurrent]
    exact M.outsideHole current huStep
  have huPreviousOriginal : G.Adj u (C.a r) := by
    rw [← A.removed_eq previous]
    exact huPreviousRemoved
  have huNotCurrentOriginal :
      ¬G.Adj u (C1.a (C1.next r)) := by
    rw [← hCurrentRemoved]
    exact hmem.2.2.2
  by_cases huCommon :
      G.Adj u (C1.b (C1.next r))
  · refine
      ⟨previous, by simpa [previous] using hij, Or.inl ?_⟩
    have hwPreviousIntroduced :
        G.Adj (D.deformation.step previous).introduced
          (C1.b (C1.next r)) := by
      simpa [C, C1, r, hprevious] using
        C1.adj_a_b_next r
    have hwCurrentRemoved :
        G.Adj
          ((D.deformation.step current).before.vertex
            (D.deformation.step current).removedIndex)
          (C1.b (C1.next r)) := by
      rw [hCurrentRemoved]
      exact C1.adj_a_b (C1.next r)
    exact D.adj_previous_introduced_of_adj_common
      L hclaw hs previous
      (by simpa [current] using hij)
      huOutside
      hwPreviousIntroduced
      hwCurrentRemoved
      huCommon
      (by simpa [current] using hmem.2.2.2)
  · have hfourLocal :=
      C.four_previous_neighbors_of_halfLength_three_of_not_common
        hclaw hprevious hcurrent huOutsideCurrent
        huPreviousOriginal hmem.2.1
        huNotCurrentOriginal huCommon
    have houtsidePrevious :
        u ∉ Set.range
          (D.deformation.step previous).before.vertex := by
      rw [← A.carrier_eq previous]
      exact hfourLocal.1
    have haMem :
        C.a r ∈ Set.range
          (D.deformation.step previous).before.vertex := by
      rw [← A.carrier_eq previous]
      exact C.a_mem_carrier r
    have hbMem :
        C.b r ∈ Set.range
          (D.deformation.step previous).before.vertex := by
      rw [← A.carrier_eq previous]
      exact C.b_mem_carrier r
    have hbFarMem :
        C.b (C.next (C.next r)) ∈ Set.range
          (D.deformation.step previous).before.vertex := by
      rw [← A.carrier_eq previous]
      exact C.b_mem_carrier (C.next (C.next r))
    have haFarMem :
        C.a (C.next (C.next r)) ∈ Set.range
          (D.deformation.step previous).before.vertex := by
      rw [← A.carrier_eq previous]
      exact C.a_mem_carrier (C.next (C.next r))
    obtain ⟨p, hp⟩ := haMem
    obtain ⟨q, hq⟩ := hbMem
    obtain ⟨x, hx⟩ := hbFarMem
    obtain ⟨y, hy⟩ := haFarMem
    have hax :
        C.a r ≠ C.a (C.next (C.next r)) := by
      intro hEq
      exact C.next_next_ne (by omega) r
        (C.a_injective hEq).symm
    have hbx :
        C.b r ≠ C.b (C.next (C.next r)) :=
      C.b_ne_next_next (by omega) r
    have hpq : p ≠ q := by
      intro hpq
      exact C.color_disjoint r r
        (hp.symm.trans ((congrArg
          (D.deformation.step previous).before.vertex hpq).trans hq))
    have hpx : p ≠ x := by
      intro hpx
      exact C.color_disjoint r (C.next (C.next r))
        (hp.symm.trans ((congrArg
          (D.deformation.step previous).before.vertex hpx).trans hx))
    have hpy : p ≠ y := by
      intro hpy
      exact hax
        (hp.symm.trans ((congrArg
          (D.deformation.step previous).before.vertex hpy).trans hy))
    have hqx : q ≠ x := by
      intro hqx
      exact hbx
        (hq.symm.trans ((congrArg
          (D.deformation.step previous).before.vertex hqx).trans hx))
    have hqy : q ≠ y := by
      intro hqy
      exact (C.color_disjoint (C.next (C.next r)) r).symm
        (hq.symm.trans ((congrArg
          (D.deformation.step previous).before.vertex hqy).trans hy))
    have hxy : x ≠ y := by
      intro hxy
      exact (C.color_disjoint
        (C.next (C.next r)) (C.next (C.next r))).symm
        (hx.symm.trans ((congrArg
          (D.deformation.step previous).before.vertex hxy).trans hy))
    refine
      ⟨previous, by simpa [previous] using hij, Or.inr ?_⟩
    refine
      ⟨houtsidePrevious, p, q, x, y,
        hpq, hpx, hpy, hqx, hqy, hxy, ?_, ?_, ?_, ?_⟩
    · rw [hp]
      exact huPreviousOriginal
    · rw [hq]
      exact hfourLocal.2.1
    · rw [hx]
      exact hfourLocal.2.2.1
    · rw [hy]
      exact hfourLocal.2.2.2

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
