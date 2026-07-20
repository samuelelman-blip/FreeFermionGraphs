import FreeFermionGraphs.Lemma11BOrdinaryPersistentNeighbors

/-!
# Lemma 11(b): the exceptional six-cycle after later replacements

The exceptional half-length-three branch has degree four immediately after
its current replacement.  At most one replacement can follow: a fourth
consecutive replacement on three alternating `a`-coordinates would remove
the first clone again, contradicting the injective Definition 19 path order.

If that one later replacement exists, claw-freeness forces adjacency to its
clone, so it replaces an adjacent original by an adjacent clone and preserves
the degree.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V}
variable {O : FixedPairingPathFamily G} {Cprime : Set V}

namespace ConcretePathDeformation

/-- Four consecutive replacements cannot occur on three alternating
`a`-coordinates. -/
theorem no_four_consecutive_steps_of_halfLength_three
    {D : ConcretePathDeformation O Cprime}
    (A : D.AlternatingLabelingSequence 3)
    (L : Definition19GlobalOverlapPathOrder D)
    {i₀ i₁ i₂ i₃ : Fin D.deformation.stepCount}
    (h₀₁ : i₀.val + 1 = i₁.val)
    (h₁₂ : i₁.val + 1 = i₂.val)
    (h₂₃ : i₂.val + 1 = i₃.val) :
    False := by
  let C0 : EvenHoleLabeling G 3 := A.labeling i₀
  let r0 : Fin 3 := A.removedAIndex i₀
  have hr1 : A.removedAIndex i₁ = C0.next r0 := by
    simpa [C0, r0] using A.removed_index_next h₀₁
  have hr2 :
      A.removedAIndex i₂ = C0.next (C0.next r0) := by
    have h := A.removed_index_next h₁₂
    rw [A.transport_eq h₀₁] at h
    rw [hr1] at h
    simpa [C0, r0] using h
  have hr3 :
      A.removedAIndex i₃ =
        C0.next (C0.next (C0.next r0)) := by
    have h := A.removed_index_next h₂₃
    rw [A.transport_eq h₁₂] at h
    have h' :
        A.removedAIndex i₃ =
          (A.labeling i₁).next (A.removedAIndex i₂) := by
      simpa using h
    rw [hr2] at h'
    calc
      A.removedAIndex i₃ =
          (A.labeling i₁).next (C0.next (C0.next r0)) := h'
      _ = C0.next (C0.next (C0.next r0)) := by
        rw [A.transport_eq h₀₁]
        rfl
  have hr3' : A.removedAIndex i₃ = r0 := by
    rw [hr3, C0.next_next_next_eq_of_three r0]
  have hAt1 :
      (A.labeling i₁).a r0 =
        (D.deformation.step i₀).introduced := by
    rw [A.transport_eq h₀₁]
    simpa [C0, r0] using
      (EvenHoleLabeling.deform_a_at
        (A.labeling i₀) (A.cloneAt i₀))
  have hAt2 :
      (A.labeling i₂).a r0 = (A.labeling i₁).a r0 := by
    rw [A.transport_eq h₁₂]
    apply EvenHoleLabeling.deform_a_away
    intro heq
    have : r0 = C0.next r0 := by
      simpa [hr1] using heq
    exact C0.next_ne r0 this.symm
  have hAt3 :
      (A.labeling i₃).a r0 = (A.labeling i₂).a r0 := by
    rw [A.transport_eq h₂₃]
    apply EvenHoleLabeling.deform_a_away
    intro heq
    have : r0 = C0.next (C0.next r0) := by
      simpa [hr2] using heq
    exact C0.next_next_ne (by omega) r0 this.symm
  have hbad :
      (D.deformation.step i₀).introduced =
        (D.deformation.step i₃).before.vertex
          (D.deformation.step i₃).removedIndex := by
    calc
      (D.deformation.step i₀).introduced =
          (A.labeling i₁).a r0 := hAt1.symm
      _ = (A.labeling i₂).a r0 := hAt2.symm
      _ = (A.labeling i₃).a r0 := hAt3.symm
      _ = (A.labeling i₃).a (A.removedAIndex i₃) := by
        rw [hr3']
      _ = (D.deformation.step i₃).before.vertex
          (D.deformation.step i₃).removedIndex :=
        (A.removed_eq i₃).symm
  exact (D.introduced_ne_later_removed L i₀ i₃ (by omega)) hbad

/-- In the six-cycle case, any step strictly after `s` is necessarily the
single step `s + 1`. -/
theorem later_index_eq_succ_of_halfLength_three
    {D : ConcretePathDeformation O Cprime}
    (A : D.AlternatingLabelingSequence 3)
    (L : Definition19GlobalOverlapPathOrder D)
    {s : Nat}
    (previous : Fin D.deformation.stepCount)
    (hprevious : previous.val + 1 = s)
    (j : Fin D.deformation.stepCount)
    (hsj : s < j.val) :
    j.val = s + 1 := by
  by_contra hne
  have hs : s < D.deformation.stepCount := by omega
  have hfuture : s + 1 < D.deformation.stepCount := by omega
  have hwrap : s + 2 < D.deformation.stepCount := by omega
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  let future : Fin D.deformation.stepCount := ⟨s + 1, hfuture⟩
  let wrap : Fin D.deformation.stepCount := ⟨s + 2, hwrap⟩
  exact D.no_four_consecutive_steps_of_halfLength_three
    A L
    (i₀ := previous) (i₁ := current)
    (i₂ := future) (i₃ := wrap)
    (by simpa [current] using hprevious)
    (by rfl) (by rfl)

/-- In the exceptional six-cycle branch, the only possible later
replacement removes the far `a`-vertex.  The claw displayed in the paper
forces `u` to neighbor its clone as well, so the replacement preserves the
degree. -/
theorem laterReplacementAdjacencyAgreement_of_halfLength_three_of_not_adj_previous
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
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (previous : Fin D.deformation.stepCount)
    (hprevious : previous.val + 1 = s)
    (huNotPrevious :
      ¬G.Adj u (D.deformation.step previous).introduced) :
    D.LaterReplacementAdjacencyAgreement s u := by
  have hs : s < D.deformation.stepCount :=
    D.index_lt_of_mem_dependentAt hu
  let current : Fin D.deformation.stepCount := ⟨s, hs⟩
  have hij : previous.val + 1 = current.val := by
    simpa [current] using hprevious
  let C : EvenHoleLabeling G 3 := A.labeling previous
  let r : Fin 3 := A.removedAIndex previous
  let hpreviousClone := A.cloneAt previous
  let C1 : EvenHoleLabeling G 3 := C.deform hpreviousClone
  have hlabelCurrent : A.labeling current = C1 := by
    simpa [C, C1, hpreviousClone] using A.transport_eq hij
  have hrCurrent :
      A.removedAIndex current = C1.next r := by
    have h := A.removed_index_next hij
    simpa [C, C1, r, hpreviousClone] using h
  have hcurrent :
      C1.CloneAt
        (D.deformation.step current).introduced
        (C1.next r) := by
    have h := A.cloneAt current
    rw [hlabelCurrent] at h
    rw [hrCurrent] at h
    exact h
  have hcarrierCurrent :
      C1.carrier =
        Set.range (D.deformation.step current).before.vertex := by
    rw [← hlabelCurrent]
    exact A.carrier_eq current
  have hCurrentRemoved :
      (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex =
        C1.a (C1.next r) := by
    calc
      (D.deformation.step current).before.vertex
          (D.deformation.step current).removedIndex =
          (A.labeling current).a (A.removedAIndex current) :=
        A.removed_eq current
      _ = C1.a (C1.next r) := by rw [hlabelCurrent, hrCurrent]
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
  obtain ⟨t, ht, hts, huPreviousRemoved'⟩ :=
    D.adj_previous_removed_of_outside_commuting
      M L hclaw horder hopposite hu huOutside hnotAnti
  have htval : t = previous.val := by omega
  have htp :
      (⟨t, ht⟩ : Fin D.deformation.stepCount) = previous := by
    apply Fin.ext
    exact htval
  have huPreviousOriginal : G.Adj u (C.a r) := by
    have huPreviousRemoved :
        G.Adj u
          ((D.deformation.step previous).before.vertex
            (D.deformation.step previous).removedIndex) := by
      rw [← htp]
      exact huPreviousRemoved'
    rw [← A.removed_eq previous]
    simpa [C, r] using huPreviousRemoved
  have huNotCurrentOriginal :
      ¬G.Adj u (C1.a (C1.next r)) := by
    rw [← hCurrentRemoved]
    exact hmem.2.2.2
  have huNotCommon : ¬G.Adj u (C1.b (C1.next r)) := by
    intro huCommon
    have hwPreviousIntroduced :
        G.Adj (D.deformation.step previous).introduced
          (C1.b (C1.next r)) := by
      simpa [C, C1, r, hpreviousClone] using
        hpreviousClone.adj_b_next
    have hwCurrentRemoved :
        G.Adj
          ((D.deformation.step current).before.vertex
            (D.deformation.step current).removedIndex)
          (C1.b (C1.next r)) := by
      rw [hCurrentRemoved]
      exact C1.adj_a_b (C1.next r)
    exact huNotPrevious
      (D.adj_previous_introduced_of_adj_common
        L hclaw hs previous hprevious huOutside
        hwPreviousIntroduced hwCurrentRemoved huCommon
        (by simpa [current] using hmem.2.2.2))
  have hfourLocal :=
    C.four_previous_neighbors_of_halfLength_three_of_not_common
      hclaw hpreviousClone hcurrent huOutsideCurrent
      huPreviousOriginal hmem.2.1 huNotCurrentOriginal huNotCommon
  intro j hsj
  have hjval : j.val = s + 1 :=
    D.later_index_eq_succ_of_halfLength_three
      A L previous hprevious j hsj
  have hcj : current.val + 1 = j.val := by
    dsimp [current]
    omega
  have hrJ :
      A.removedAIndex j = C1.next (C1.next r) := by
    have h := A.removed_index_next hcj
    rw [hlabelCurrent] at h
    rw [hrCurrent] at h
    exact h
  have hrJNeCurrent :
      A.removedAIndex j ≠ A.removedAIndex current := by
    rw [hrJ, hrCurrent]
    exact C1.next_ne (C1.next r)
  have hRemovedFar :
      (D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex =
        C.a (C.next (C.next r)) := by
    calc
      (D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex =
          (A.labeling j).a (A.removedAIndex j) :=
        A.removed_eq j
      _ = ((A.labeling current).deform (A.cloneAt current)).a
          (A.removedAIndex j) := by rw [A.transport_eq hcj]
      _ = (A.labeling current).a (A.removedAIndex j) :=
        EvenHoleLabeling.deform_a_away
          (A.labeling current) (A.cloneAt current) hrJNeCurrent
      _ = C1.a (C1.next (C1.next r)) := by
        rw [hlabelCurrent, hrJ]
      _ = C.a (C.next (C.next r)) := by
        have hne : C.next (C.next r) ≠ r :=
          C.next_next_ne (by omega) r
        simpa [C1] using C.deform_a_away hpreviousClone hne
  have huRemovedJ :
      G.Adj u
        ((D.deformation.step j).before.vertex
          (D.deformation.step j).removedIndex) := by
    rw [hRemovedFar]
    exact hfourLocal.2.2.2
  have hbFuture :
      (A.labeling j).b
          ((A.labeling j).next (A.removedAIndex j)) =
        C.b r := by
    rw [A.transport_eq hcj]
    change
      (A.labeling current).b
          ((A.labeling current).next (A.removedAIndex j)) =
        C.b r
    rw [hlabelCurrent]
    rw [hrJ]
    simpa [C1] using
      congrArg C.b (C.next_next_next_eq_of_three r)
  have hCenterPrevious :
      G.Adj (C.b r)
        (D.deformation.step previous).introduced := by
    exact hpreviousClone.adj_b.symm
  have hCenterFuture :
      G.Adj (C.b r) (D.deformation.step j).introduced := by
    have h := (A.cloneAt j).adj_b_next
    rw [hbFuture] at h
    exact h.symm
  have huNePrevious :
      u ≠ (D.deformation.step previous).introduced := by
    intro hEq
    apply huOutside
    refine ⟨L.introducedPathIndex previous, ?_⟩
    exact (L.introduced_eq previous).trans hEq.symm
  have huNeFuture :
      u ≠ (D.deformation.step j).introduced := by
    intro hEq
    apply huOutside
    refine ⟨L.introducedPathIndex j, ?_⟩
    exact (L.introduced_eq j).trans hEq.symm
  have hPreviousFutureNe :
      (D.deformation.step previous).introduced ≠
        (D.deformation.step j).introduced :=
    D.introduced_ne_later_introduced L previous j (by omega)
  have hPreviousFutureNotAdj :
      ¬G.Adj (D.deformation.step previous).introduced
        (D.deformation.step j).introduced := by
    intro hadj
    have hpath :
        G.Adj
          (D.path.vertex (L.introducedPathIndex previous))
          (D.path.vertex (L.introducedPathIndex j)) := by
      simpa [L.introduced_eq] using hadj
    rcases (D.path.adj_iff
      (L.introducedPathIndex previous)
      (L.introducedPathIndex j)).1 hpath with h | h
    · have hp := L.introduced_index_val previous
      have hj := L.introduced_index_val j
      omega
    · have hp := L.introduced_index_val previous
      have hj := L.introduced_index_val j
      omega
  have huIntroducedJ :
      G.Adj u (D.deformation.step j).introduced := by
    by_contra huNotFuture
    rcases hclaw
        hfourLocal.2.1.symm
        hCenterPrevious hCenterFuture
        huNePrevious huNeFuture hPreviousFutureNe with
      huPrevious | huFuture | hPreviousFuture
    · exact huNotPrevious huPrevious
    · exact huNotFuture huFuture
    · exact hPreviousFutureNotAdj hPreviousFuture
  constructor
  · intro _
    exact huRemovedJ
  · intro _
    exact huIntroducedJ

/-- The half-length-three outside branch now has an unconditional final
degree-four conclusion: the ordinary branch uses the four persistent final
neighbors, while the exceptional branch uses the proved later-replacement
agreement. -/
theorem finalDegree_eq_four_of_halfLength_three
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence 3)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierOverlapColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 := by
  obtain ⟨previous, hprevious, hbranch⟩ :=
    D.previous_introduced_or_current_degreeAfter_eq_four_of_halfLength_three
      M A L hclaw hInitialEven horder hopposite
      hu huOutside hnotAnti
  by_cases huPrevious :
      G.Adj u (D.deformation.step previous).introduced
  · exact
      D.finalDegree_eq_four_of_adj_previous_introduced
        M A L hclaw hInitialEven hcolors horder hopposite
        hu huOutside hnotAnti previous.isLt
        (by omega) huPrevious
  · have hcurrent :
        (D.deformation.step
          ⟨s, D.index_lt_of_mem_dependentAt hu⟩).degreeAfter u = 4 := by
      rcases hbranch with huPrevious' | hcurrent
      · exact (huPrevious huPrevious').elim
      · exact hcurrent
    have hagreement : D.LaterReplacementAdjacencyAgreement s u :=
      D.laterReplacementAdjacencyAgreement_of_halfLength_three_of_not_adj_previous
        M A L hclaw horder hopposite
        hu huOutside hnotAnti previous hprevious huPrevious
    exact D.finalDegree_eq_four_of_current_and_laterAgreement
      (D.index_lt_of_mem_dependentAt hu) hcurrent hagreement

/-- All alternating half-lengths are now covered for an outside-path
commuting dependent vertex. -/
theorem outside_finalDegree_eq_four_of_alternating
    {k : Nat} (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (hcycle : A.HasFullCyclicOrder)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hInitialEven : Even D.initialHole.card)
    (hcolors : O.PrimeCarrierOverlapColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u) :
    D.finalDegree s u = 4 := by
  by_cases hkTwo : k = 2
  · subst k
    obtain ⟨previous, hprevious, huPrevious⟩ :=
      D.adj_previous_introduced_of_halfLength_two
        M A L hclaw horder hopposite
        hu huOutside hnotAnti
    exact
      D.finalDegree_eq_four_of_adj_previous_introduced
        M A L hclaw hInitialEven hcolors horder hopposite
        hu huOutside hnotAnti previous.isLt
        (by omega) huPrevious
  by_cases hkThree : k = 3
  · subst k
    exact
      D.finalDegree_eq_four_of_halfLength_three
        M A L hclaw hInitialEven hcolors horder hopposite
        hu huOutside hnotAnti
  have hk : 3 < k := by
    have htwo := (A.labeling D.firstIndex).two_le
    omega
  obtain ⟨previous, hprevious, huPrevious⟩ :=
    D.adj_previous_introduced_of_three_lt
      M A hcycle hk L hclaw horder hopposite
      hu huOutside hnotAnti
  exact
    D.finalDegree_eq_four_of_adj_previous_introduced
      M A L hclaw hInitialEven hcolors horder hopposite
      hu huOutside hnotAnti previous.isLt
      (by omega) huPrevious

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
