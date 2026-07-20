import FreeFermionGraphs.Lemma11BPrimeHoleCoordinates

/-!
# Lemma 11(b): path descent in the ordinary outside branch

The ordinary outside branch first produces the other prime-hole neighbor
of the preceding introduced vertex.  It is either Definition 20 dependent
one step earlier, or it also meets the preceding removed vertex.  In the
latter case the paper moves one step farther back.  The final predecessor
need not share one `C_b` neighbor with the current vertex; instead the two
are joined by the five-vertex chain displayed in the proof.  This module
formalizes that chain as `SharesPath`.
-/

universe u

variable {V : Type u}

namespace SimpleGraph

namespace FixedPairingPathFamily

variable {G : SimpleGraph V} {O : FixedPairingPathFamily G}
  {Cprime : Set V}

namespace ConcretePathDeformation

/-- In the ordinary branch there is a Definition 20 predecessor one or two
steps earlier in the same fixed-pairing path component. -/
theorem ordinary_oneOrTwoStepDefinition20_sharesPath
    {k kPrime : Nat}
    (D : ConcretePathDeformation O Cprime)
    (M : D.MechanicalData)
    (A : D.AlternatingLabelingSequence k)
    (P : D.PrimeAlternatingHoleData kPrime)
    (L : Definition19GlobalOverlapPathOrder D)
    (hclaw : G.IsClawFree)
    (hcolors : O.PrimeCarrierExactlyColored Cprime)
    (horder : Definition19PathOrder M)
    (hopposite : D.BaseOppositeEndpointNonadjacency)
    {s t : Nat} {u : V}
    (hu : u ∈ D.dependentAt s)
    (huOutside : u ∉ Set.range D.path.vertex)
    (hnotAnti : ¬D.path.AnticommutesWith u)
    (ht : t < D.deformation.stepCount)
    (hts : Nat.succ t = s)
    (huPreviousIntroduced :
      G.Adj u (D.deformation.step ⟨t, ht⟩).introduced) :
    (∃ u' : V,
      D.Definition20DependentAt t u' ∧
      O.SharesPath u' u) ∨
    (∃ e : Nat, Nat.succ e = t ∧
      ∃ u' : V,
        D.Definition20DependentAt e u' ∧
        O.SharesPath u' u) := by
  obtain himmediate | hconfig :=
    D.ordinary_previousDefinition20_or_twoStepConfiguration
      M A P L hclaw hcolors horder hopposite
      hu huOutside hnotAnti ht hts huPreviousIntroduced
  · obtain ⟨u', w, hu'Definition20, hwCb, hu'w, huw⟩ :=
      himmediate
    have hu'Mem : u' ∈ D.dependentAt t :=
      (D.mem_dependentAt_iff_definition20).2 hu'Definition20
    exact Or.inl ⟨u', hu'Definition20,
      M.sharesPath_of_common_cb
        (M.dependent_mem_cd hu'Mem) (M.dependent_mem_cd hu)
        hwCb hu'w huw⟩
  · obtain ⟨ht', u1, w, hu1Prime, hu1Cd,
        hu1PreviousIntroduced, hu1NeU, hu1NotU,
        hu1PreviousRemoved, hwCb, hu1w, huw⟩ := hconfig
    let previous : Fin D.deformation.stepCount := ⟨t, ht'⟩
    have huPreviousIntroduced' :
        G.Adj u (D.deformation.step previous).introduced := by
      simpa [previous] using huPreviousIntroduced
    have hs : s < D.deformation.stepCount :=
      D.index_lt_of_mem_dependentAt hu
    let current : Fin D.deformation.stepCount := ⟨s, hs⟩
    have hpc : previous.val + 1 = current.val := by
      dsimp [previous, current]
      omega
    obtain ⟨earlier, hep, huEarlierRemoved,
        huNotEarlierIntroduced⟩ :=
      D.earlier_original_adj_and_clone_not_adj_of_adj_previous_introduced
        M L hclaw horder hopposite
        hu huOutside hnotAnti ht' hts huPreviousIntroduced'
    have hk : 2 < k :=
      D.two_lt_halfLength_of_three_consecutive_steps A L hep hpc
    have hkPrime : 2 < kPrime :=
      P.two_lt_halfLength_of_three_consecutive_introductions
        L hep hpc
    let C : EvenHoleLabeling G k := A.labeling previous
    let r : Fin k := A.removedAIndex previous
    have huBoth :
        G.Adj u (C.b r) ∧ G.Adj u (C.b (C.next r)) := by
      simpa [C, r, previous] using
        D.adj_two_persistent_b_of_adj_previous_introduced
          M A L hclaw hcolors horder hopposite
          hu huOutside hnotAnti ht' hts huPreviousIntroduced'
    have huStep :
        u ∈ (D.deformation.step current).dependentSet := by
      simpa [current] using
        D.mem_step_dependentSet_of_mem_dependentAt hu
    have humem :=
      (ConcreteDeformationStep.mem_dependentSet
        (D.deformation.step current)).1 huStep
    have huPrime : u ∈ Cprime := humem.1
    have huCd : u ∈ O.Cd := M.dependent_mem_cd hu
    obtain ⟨qu, huEqB⟩ :=
      P.eq_b_of_mem_prime_and_adj_introduced
        current huPrime humem.2.1
    obtain ⟨q1, hu1EqB⟩ :=
      P.eq_b_of_mem_prime_and_adj_introduced
        previous hu1Prime hu1PreviousIntroduced
    have hqNe : q1 ≠ qu := by
      intro h
      apply hu1NeU
      rw [hu1EqB, huEqB, h]
    have hpreviousCurrentPrimeIndex :
        P.introducedIndex previous ≠
          P.introducedIndex current := by
      intro h
      have hEq :
          (D.deformation.step previous).introduced =
            (D.deformation.step current).introduced := by
        rw [← P.introduced_eq previous,
          ← P.introduced_eq current, h]
      exact D.introduced_ne_later_introduced
        L previous current (by omega) hEq
    have hquAtPrevious :
        qu = P.introducedIndex previous ∨
          qu = P.labeling.next (P.introducedIndex previous) := by
      apply (P.labeling.adj_ab_iff
        (P.introducedIndex previous) qu).1
      rw [P.introduced_eq previous, ← huEqB]
      exact huPreviousIntroduced'.symm
    have hq1AtPrevious :
        q1 = P.introducedIndex previous ∨
          q1 = P.labeling.next (P.introducedIndex previous) := by
      apply (P.labeling.adj_ab_iff
        (P.introducedIndex previous) q1).1
      rw [P.introduced_eq previous, ← hu1EqB]
      exact hu1PreviousIntroduced.symm
    have hquAtCurrent :
        qu = P.introducedIndex current ∨
          qu = P.labeling.next (P.introducedIndex current) := by
      apply (P.labeling.adj_ab_iff
        (P.introducedIndex current) qu).1
      rw [P.introduced_eq current, ← huEqB]
      exact humem.2.1.symm
    have hu1NotCurrentIntroduced :
        ¬G.Adj u1 (D.deformation.step current).introduced := by
      intro hu1Current
      have hq1AtCurrent :
          q1 = P.introducedIndex current ∨
            q1 = P.labeling.next (P.introducedIndex current) := by
        apply (P.labeling.adj_ab_iff
          (P.introducedIndex current) q1).1
        rw [P.introduced_eq current, ← hu1EqB]
        exact hu1Current.symm
      exact
        (other_b_not_adjacent_other_a P.labeling
          hkPrime hpreviousCurrentPrimeIndex
          hquAtPrevious hq1AtPrevious hqNe hquAtCurrent)
          hq1AtCurrent
    have hb0Before :
        C.b r ∈ Set.range
          (D.deformation.step previous).before.vertex := by
      rw [← A.carrier_eq previous]
      exact C.b_mem_carrier r
    have hb0Cb : C.b r ∈ O.Cb := by
      rcases (M.stepGeometry previous).before_subset hb0Before with
        hb0Ca | hb0Cb
      · exact ((M.stepGeometry previous).ca_independent
          (M.stepGeometry previous).removed_ca hb0Ca
          (by
            rw [A.removed_eq previous]
            exact C.adj_a_b r)).elim
      · exact hb0Cb
    let hpreviousClone := A.cloneAt previous
    let C1 : EvenHoleLabeling G k := C.deform hpreviousClone
    have hlabelCurrent : A.labeling current = C1 := by
      simpa [C, C1, hpreviousClone] using A.transport_eq hpc
    have hrCurrent : A.removedAIndex current = C1.next r := by
      have h := A.removed_index_next hpc
      simpa [C, C1, r, hpreviousClone] using h
    have hcurrentClone :
        C1.CloneAt
          (D.deformation.step current).introduced
          (C1.next r) := by
      have h := A.cloneAt current
      rw [hlabelCurrent] at h
      rw [hrCurrent] at h
      exact h
    have hCurrentIntroducedNotB0 :
        ¬G.Adj (D.deformation.step current).introduced (C.b r) := by
      intro hAdj
      have hb0Carrier : C.b r ∈ C1.carrier := by
        simpa [C1] using C1.b_mem_carrier r
      rcases (hcurrentClone.adj_iff (C.b r) hb0Carrier).1 hAdj with
        hEq | hOriginal
      · exact C1.color_disjoint (C1.next r) r
          (by simpa [C1] using hEq.symm)
      · exact C1.not_adj_a_next_b hk r
          (by simpa [C1] using hOriginal)
    have hu1B0 : G.Adj u1 (C.b r) := by
      have hpreviousRemovedB0 :
          G.Adj
            ((D.deformation.step previous).before.vertex
              (D.deformation.step previous).removedIndex)
            (C.b r) := by
        rw [A.removed_eq previous]
        exact C.adj_a_b r
      have hCurrentNeU1 :
          (D.deformation.step current).introduced ≠ u1 := by
        intro h
        apply (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
          (hcolors hu1Prime) hu1Cd).2.2
        rw [← h]
        exact (M.stepGeometry current).base.introduced_cc
      have hCurrentNeB0 :
          (D.deformation.step current).introduced ≠ C.b r := by
        intro h
        apply hcurrentClone.outside
        rw [h]
        simpa [C1] using C1.b_mem_carrier r
      have hu1NeB0 : u1 ≠ C.b r := by
        intro h
        apply (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
          (hcolors hu1Prime) hu1Cd).2.1
        rw [h]
        exact hb0Cb
      have hpreviousRemovedCurrentIntroduced :
          G.Adj
            ((D.deformation.step previous).before.vertex
              (D.deformation.step previous).removedIndex)
            (D.deformation.step current).introduced := by
        rw [← L.removed_eq previous, ← L.introduced_eq current]
        apply (D.path.adj_iff
          (L.removedPathIndex previous)
          (L.introducedPathIndex current)).2
        left
        have hp := L.removed_index_val previous
        have hc := L.introduced_index_val current
        omega
      rcases hclaw hpreviousRemovedCurrentIntroduced
          hu1PreviousRemoved.symm hpreviousRemovedB0
          hCurrentNeU1 hCurrentNeB0 hu1NeB0 with
        hCurrentU1 | hCurrentB0 | hu1B0
      · exact (hu1NotCurrentIntroduced hCurrentU1.symm).elim
      · exact (hCurrentIntroducedNotB0 hCurrentB0).elim
      · exact hu1B0
    have hEarlierIntroducedB0 :
        G.Adj (D.deformation.step earlier).introduced (C.b r) := by
      let C0 : EvenHoleLabeling G k := A.labeling earlier
      let r0 : Fin k := A.removedAIndex earlier
      have hbEq : C.b r = C0.b (C0.next r0) := by
        dsimp [C, r, C0, r0]
        rw [A.removed_index_next hep, A.transport_eq hep]
        rfl
      rw [hbEq]
      exact (A.cloneAt earlier).adj_b_next
    have huNeEarlierIntroduced :
        u ≠ (D.deformation.step earlier).introduced := by
      intro h
      apply huOutside
      refine ⟨L.introducedPathIndex earlier, ?_⟩
      exact (L.introduced_eq earlier).trans h.symm
    have hu1NeEarlierIntroduced :
        u1 ≠ (D.deformation.step earlier).introduced := by
      intro h
      apply (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
        (hcolors hu1Prime) hu1Cd).2.2
      rw [h]
      exact (M.stepGeometry earlier).base.introduced_cc
    have hu1EarlierIntroduced :
        G.Adj u1 (D.deformation.step earlier).introduced := by
      rcases hclaw huBoth.1.symm hu1B0.symm
          hEarlierIntroducedB0.symm
          hu1NeU.symm huNeEarlierIntroduced
          hu1NeEarlierIntroduced with
        huu1 | huEarlier | hu1Earlier
      · exact (hu1NotU huu1.symm).elim
      · exact (huNotEarlierIntroduced huEarlier).elim
      · exact hu1Earlier
    have hu1NeEarlierRemoved :
        u1 ≠
          (D.deformation.step earlier).before.vertex
            (D.deformation.step earlier).removedIndex := by
      intro h
      apply (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
        (hcolors hu1Prime) hu1Cd).1
      rw [h]
      exact (M.stepGeometry earlier).removed_ca
    have hu1UShares : O.SharesPath u1 u :=
      M.sharesPath_of_common_cb hu1Cd huCd hwCb hu1w huw
    by_cases hu1EarlierRemoved :
        G.Adj u1
          ((D.deformation.step earlier).before.vertex
            (D.deformation.step earlier).removedIndex)
    · obtain ⟨u2, hu2Prime, hu2EarlierIntroduced,
          hu2NeU1, hu2NotU1⟩ :=
        P.exists_other_prime_neighbor
          earlier hu1Prime hu1EarlierIntroduced
      have hu2Cd : u2 ∈ O.Cd := by
        rcases (M.stepGeometry earlier).prime_subset hu2Prime with
          hu2Cc | hu2Cd
        · exact ((M.stepGeometry earlier).base.cc_independent
            hu2Cc (M.stepGeometry earlier).base.introduced_cc
            hu2EarlierIntroduced).elim
        · exact hu2Cd
      obtain ⟨q2, hu2EqB⟩ :=
        P.eq_b_of_mem_prime_and_adj_introduced
          earlier hu2Prime hu2EarlierIntroduced
      have hu2NotU : ¬G.Adj u2 u := by
        rw [hu2EqB, huEqB]
        exact P.labeling.adj_bb q2 qu
      have hu2NeU : u2 ≠ u := by
        intro h
        apply huNotEarlierIntroduced
        rw [← h]
        exact hu2EarlierIntroduced
      have hu2NeEarlierRemoved :
          u2 ≠
            (D.deformation.step earlier).before.vertex
              (D.deformation.step earlier).removedIndex := by
        intro h
        apply (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
          (hcolors hu2Prime) hu2Cd).1
        rw [h]
        exact (M.stepGeometry earlier).removed_ca
      have hu2NotEarlierRemoved :
          ¬G.Adj u2
            ((D.deformation.step earlier).before.vertex
              (D.deformation.step earlier).removedIndex) := by
        intro hu2EarlierRemoved
        rcases hclaw huEarlierRemoved.symm
            hu1EarlierRemoved.symm hu2EarlierRemoved.symm
            hu1NeU.symm hu2NeU.symm hu2NeU1.symm with
          huu1 | huu2 | hu1u2
        · exact hu1NotU huu1.symm
        · exact hu2NotU huu2.symm
        · exact hu2NotU1 hu1u2.symm
      have hu2Definition20 :
          D.Definition20DependentAt earlier.val u2 :=
        ⟨earlier.isLt, hu2Prime, hu2EarlierIntroduced,
          hu2NeEarlierRemoved, hu2NotEarlierRemoved⟩
      have hu2Mem : u2 ∈ D.dependentAt earlier.val :=
        (D.mem_dependentAt_iff_definition20).2 hu2Definition20
      have hu2Step :
          u2 ∈ (D.deformation.step earlier).dependentSet := by
        simpa using D.mem_step_dependentSet_of_mem_dependentAt hu2Mem
      obtain ⟨w2, _hw2Before, hu2w2, _hintroducedW2,
          hremovedW2, hw2Cb⟩ :=
        (D.deformation.step earlier).dependent_commonNeighbor_mem_cb
          (M.stepGeometry earlier) hclaw hu2Step
          (M.outsideHole earlier hu2Step)
      have hu2UShares : O.SharesPath u2 u := by
        by_cases huw2 : G.Adj u w2
        · exact M.sharesPath_of_common_cb hu2Cd huCd hw2Cb
            hu2w2 huw2
        · have hu1w2 : G.Adj u1 w2 := by
            have huNotCb : u ∉ O.Cb :=
              (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
                (hcolors huPrime) huCd).2.1
            have hu1NotCb : u1 ∉ O.Cb :=
              (ExactlyOneOfFour.not_mem_first_three_of_mem_fourth
                (hcolors hu1Prime) hu1Cd).2.1
            have huNeW2 : u ≠ w2 := by
              intro h
              apply huNotCb
              rw [h]
              exact hw2Cb
            have hu1NeW2 : u1 ≠ w2 := by
              intro h
              apply hu1NotCb
              rw [h]
              exact hw2Cb
            rcases hclaw huEarlierRemoved.symm
                hu1EarlierRemoved.symm hremovedW2
                hu1NeU.symm huNeW2 hu1NeW2 with
              huu1 | huw2' | hu1w2
            · exact (hu1NotU huu1.symm).elim
            · exact (huw2 huw2').elim
            · exact hu1w2
          have hu2U1Shares : O.SharesPath u2 u1 :=
            M.sharesPath_of_common_cb hu2Cd hu1Cd hw2Cb
              hu2w2 hu1w2
          have hu1Unique : O.AtMostOneContainingPath u1 :=
            O.atMostOneContainingPath_of_exactlyOne
              (hcolors hu1Prime)
          exact O.sharesPath_trans_of_atMostOne hu1Unique
            hu2U1Shares hu1UShares
      exact Or.inr ⟨earlier.val, by omega, u2,
        hu2Definition20, hu2UShares⟩
    · have hu1Definition20 :
          D.Definition20DependentAt earlier.val u1 :=
        ⟨earlier.isLt, hu1Prime, hu1EarlierIntroduced,
          hu1NeEarlierRemoved, hu1EarlierRemoved⟩
      exact Or.inr ⟨earlier.val, by omega, u1,
        hu1Definition20, hu1UShares⟩

end ConcretePathDeformation

end FixedPairingPathFamily

end SimpleGraph
