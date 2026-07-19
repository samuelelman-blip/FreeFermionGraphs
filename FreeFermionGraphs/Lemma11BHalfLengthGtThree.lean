import FreeFermionGraphs.EvenHoleFullCyclicOrder
import FreeFermionGraphs.Lemma11BCommonForcesPreviousIntroduced

/-!
# Lemma 11(b): the half-length greater-than-three obstruction

For a long alternating hole, assume an outside dependent vertex misses the
previous common `b`-vertex and the previous introduced clone.  The first
claw forces adjacency to the other neighbor `b r` of the previous removed
vertex.  Lemma 8's forced-side theorem at the current deformation then gives
adjacency to `a (next (next r))`.  The dependent vertex would consequently
center a claw with leaves `b r`, the current introduced clone, and that
two-step `a`-vertex.

Full cyclic order supplies the only extra fact needed: `b r` and
`a (next (next r))` are nonadjacent when the half-length is greater than
three.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

variable {G : SimpleGraph V}

namespace EvenHoleLabeling

/-- The complete local long-hole obstruction. -/
theorem adj_previousClone_of_three_lt
    {k : Nat}
    (C : EvenHoleLabeling G k)
    (hcycle : C.HasFullCyclicOrder)
    (hk : 3 < k)
    (hclaw : G.IsClawFree)
    {previousIntroduced currentIntroduced u : V}
    {r : Fin k}
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
          ((C.deform hprevious).next r))) :
    G.Adj u previousIntroduced := by
  let C1 : EvenHoleLabeling G k := C.deform hprevious
  have hcycle1 : C1.HasFullCyclicOrder := by
    simpa [C1] using C.hasFullCyclicOrder_deform hprevious hcycle
  have huNe_of_mem :
      ∀ {x : V}, x ∈ C1.carrier → u ≠ x := by
    intro x hx hux
    apply huOutside
    exact Set.mem_insert_iff.2
      (Or.inr (hux.symm ▸ hx))
  have huNePrevious : u ≠ previousIntroduced := by
    apply huNe_of_mem
    simpa [C1] using C1.a_mem_carrier r
  have huNeCurrentOriginal :
      u ≠ C1.a (C1.next r) := by
    exact huNe_of_mem (C1.a_mem_carrier (C1.next r))
  have hPreviousCurrentNe :
      previousIntroduced ≠ C1.a (C1.next r) := by
    intro hEq
    have haa : C1.a r = C1.a (C1.next r) := by
      simpa [C1] using hEq
    have hindices : r = C1.next r :=
      C1.a_injective haa
    exact C1.next_ne r hindices.symm
  by_contra huNotPrevious
  by_cases huCommon :
      G.Adj u (C1.b (C1.next r))
  · have hcommonPrevious :
        G.Adj (C1.b (C1.next r)) previousIntroduced := by
      simpa [C1] using (C1.adj_a_b_next r).symm
    have hcommonCurrent :
        G.Adj (C1.b (C1.next r))
          (C1.a (C1.next r)) :=
      (C1.adj_a_b (C1.next r)).symm
    have hPreviousCurrentNotAdj :
        ¬G.Adj previousIntroduced
          (C1.a (C1.next r)) := by
      simpa [C1] using C1.adj_aa r (C1.next r)
    rcases hclaw
        huCommon.symm
        hcommonPrevious
        hcommonCurrent
        huNePrevious huNeCurrentOriginal hPreviousCurrentNe with
      huPrevious | huCurrent | hPreviousCurrent
    · exact huNotPrevious huPrevious
    · exact huNotCurrentOriginal (by
        simpa [C1] using huCurrent)
    · exact hPreviousCurrentNotAdj hPreviousCurrent
  · have huNeB : u ≠ C.b r := by
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
        huB | huCommon' | hbb
      · exact huB
      · exact huCommon (by
          simpa [C1] using huCommon')
      · exact (C.adj_bb r (C.next r) hbb).elim
    have hside :=
      hcurrent.dependent_forces_side
        hclaw huOutside
        (Or.inl
          ⟨huCurrentIntroduced,
            by simpa [C1] using huNotCurrentOriginal⟩)
    have huT :
        G.Adj u (C1.a (C1.next (C1.next r))) := by
      rcases hside with hleft | hright
      · exact (huCommon (by
          simpa [C1] using hleft.1)).elim
      · exact hright.2
    have hCurrentNotB :
        ¬G.Adj currentIntroduced (C1.b r) := by
      intro hAdj
      rcases
          (hcurrent.adj_iff
            (C1.b r) (C1.b_mem_carrier r)).1 hAdj with
        hEq | hOriginal
      · exact C1.color_disjoint (C1.next r) r hEq.symm
      · exact C1.not_adj_a_next_b (by omega) r hOriginal
    have hBNotT :
        ¬G.Adj (C1.b r)
          (C1.a (C1.next (C1.next r))) := by
      intro hAdj
      exact C1.not_adj_a_next_next_b
        hcycle1 hk r hAdj.symm
    have hCurrentNotT :
        ¬G.Adj currentIntroduced
          (C1.a (C1.next (C1.next r))) := by
      exact hcurrent.not_adj_a_next
    have hBCurrentNe : C1.b r ≠ currentIntroduced := by
      intro hEq
      apply hcurrent.outside
      rw [← hEq]
      exact C1.b_mem_carrier r
    have hBTNe :
        C1.b r ≠ C1.a (C1.next (C1.next r)) :=
      (C1.color_disjoint (C1.next (C1.next r)) r).symm
    have hCurrentTNe :
        currentIntroduced ≠
          C1.a (C1.next (C1.next r)) := by
      intro hEq
      apply hcurrent.outside
      rw [hEq]
      exact C1.a_mem_carrier (C1.next (C1.next r))
    rcases hclaw
        (by simpa [C1] using huB)
        huCurrentIntroduced
        huT
        hBCurrentNe hBTNe hCurrentTNe with
      hBCurrent | hBT | hCurrentT
    · exact hCurrentNotB hBCurrent.symm
    · exact hBNotT hBT
    · exact hCurrentNotT hCurrentT

end EvenHoleLabeling

namespace FixedPairingPathFamily

variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- Every labeling in a transported sequence has the paper's full cyclic
order. -/
def AlternatingLabelingSequence.HasFullCyclicOrder
    {k : Nat} {D : ConcretePathDeformation O Cprime}
    (A : D.AlternatingLabelingSequence k) : Prop :=
  ∀ i : Fin D.deformation.stepCount,
    (A.labeling i).HasFullCyclicOrder

/-- The long-hole obstruction specialized to consecutive concrete
deformation steps. -/
theorem adj_previous_introduced_of_three_lt
    {k : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (hcycle : A.HasFullCyclicOrder)
    (hk : 3 < k)
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
  let C : EvenHoleLabeling G k := A.labeling previous
  let r : Fin k := A.removedAIndex previous
  let hprevious := A.cloneAt previous
  let C1 : EvenHoleLabeling G k := C.deform hprevious
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
    have hnot :
        ¬G.Adj u
          ((A.labeling current).a
            (A.removedAIndex current)) := by
      rw [← A.removed_eq current]
      exact hmem.2.2.2
    rw [A.transport_eq hij] at hnot
    rw [A.removed_index_next hij] at hnot
    simpa [C, C1, r, hprevious] using hnot
  have huPreviousIntroduced :
      G.Adj u (D.deformation.step previous).introduced := by
    exact C.adj_previousClone_of_three_lt
      (hcycle previous) hk hclaw
      hprevious hcurrent huOutsideCurrent
      huPreviousOriginal hmem.2.1 huNotCurrentOriginal
  exact
    ⟨previous, by simpa [previous] using hij,
      huPreviousIntroduced⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
